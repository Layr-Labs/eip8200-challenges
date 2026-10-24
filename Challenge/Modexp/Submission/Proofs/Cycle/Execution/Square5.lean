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

def squareColumn5part0Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def squareColumn5part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 64
  let v3 : UInt256 := MachineState.readWord s.memory 32
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + v1
  {s with pc := UInt256.ofNat 6803, memory := s.memory, stack := v5 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest}

theorem squareColumn5part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part0Program {s with pc := UInt256.ofNat 6793, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: rest} =
      some (squareColumn5part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part0Program, squareColumn5part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha64, hf64]


def squareColumn5part1Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn5part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := UInt256.mulMod x3 x1 x2
  let v2 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 6812, memory := s.memory, stack := x9 :: v2 :: x13 :: v1 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn5part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part1Program {s with pc := UInt256.ofNat 6803, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn5part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part1Program, squareColumn5part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def squareColumn5part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def squareColumn5part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := UInt256.mulMod x11 v2 x14
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6821, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem squareColumn5part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part2Program {s with pc := UInt256.ofNat 6812, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (squareColumn5part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part2Program, squareColumn5part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]


def squareColumn5part3Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn5part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := MachineState.readWord s.memory 32
  let v2 : UInt256 := UInt256.mulMod v1 v0 x11
  let v3 : UInt256 := v2 + x0
  {s with pc := UInt256.ofNat 6831, memory := s.memory, stack := v3 :: v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part3Program {s with pc := UInt256.ofNat 6821, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part3Program, squareColumn5part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha64, hf64]


def squareColumn5part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL]

def squareColumn5part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x4 + v0
  let v2 : UInt256 := x4 + x2
  let v3 : UInt256 := x11 * x13
  {s with pc := UInt256.ofNat 6839, memory := s.memory, stack := v3 :: v2 :: x3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn5part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part4Program {s with pc := UInt256.ofNat 6831, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn5part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn5part4Program, squareColumn5part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn5part5Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def squareColumn5part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x2 * x5
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 192
  {s with pc := UInt256.ofNat 6848, memory := s.memory, stack := v3 :: x9 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part5Program {s with pc := UInt256.ofNat 6839, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part5Program, squareColumn5part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def squareColumn5part6Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def squareColumn5part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := v2 * x7
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6856, memory := s.memory, stack := x17 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn5part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part6Program {s with pc := UInt256.ofNat 6848, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn5part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part6Program, squareColumn5part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def squareColumn5part7Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL]

def squareColumn5part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1216
  let v4 : UInt256 := v3 * x4
  {s with pc := UInt256.ofNat 6867, memory := s.memory, stack := v4 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part7Program {s with pc := UInt256.ofNat 6856, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part7Program, squareColumn5part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


def squareColumn5part8Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def squareColumn5part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1248
  let v2 : UInt256 := v1 * x13
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 6877, memory := s.memory, stack := x11 :: x3 :: x2 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part8Program {s with pc := UInt256.ofNat 6867, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part8Program, squareColumn5part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def squareColumn5part9Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD]

def squareColumn5part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x10 x12 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x2 x5 x11
  {s with pc := UInt256.ofNat 6885, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part9Program {s with pc := UInt256.ofNat 6877, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn5part9Program, squareColumn5part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn5part10Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def squareColumn5part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x2.toNat 32) 1088
  let v2 : UInt256 := MachineState.readWord v1 192
  {s with pc := UInt256.ofNat 6896, memory := v1, stack := v2 :: x9 :: x11 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part10Program {s with pc := UInt256.ofNat 6885, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part10Program, squareColumn5part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192, ha1088, hf1088]


def squareColumn5part11Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def squareColumn5part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.mulMod v2 x7 x12
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6904, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn5part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part11Program {s with pc := UInt256.ofNat 6896, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn5part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part11Program, squareColumn5part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def squareColumn5part12Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def squareColumn5part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.mulMod v0 x14 x9
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 6913, memory := s.memory, stack := x2 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn5part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part12Program {s with pc := UInt256.ofNat 6904, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn5part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part12Program, squareColumn5part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def squareColumn5part13Program : List Instr :=
  [.push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn5part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1216
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 6921, memory := s.memory, stack := x13 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn5part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5part13Program {s with pc := UInt256.ofNat 6913, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn5part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn5part13Program, squareColumn5part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def squareColumn5Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1088,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn5Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 word20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := MachineState.readWord s.memory 64
  let v3 : UInt256 := MachineState.readWord s.memory 32
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := v5 + v5
  let v7 : UInt256 := UInt256.mulMod word4 word2 word3
  let v8 : UInt256 := MachineState.readWord s.memory 128
  let v9 : UInt256 := UInt256.mulMod word10 v8 word14
  let v10 : UInt256 := v9 + v7
  let v11 : UInt256 := MachineState.readWord s.memory 96
  let v12 : UInt256 := UInt256.mulMod word11 v11 word14
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := MachineState.readWord s.memory 64
  let v15 : UInt256 := MachineState.readWord s.memory 32
  let v16 : UInt256 := UInt256.mulMod v15 v14 word14
  let v17 : UInt256 := v16 + v13
  let v18 : UInt256 := v17 + v17
  let v19 : UInt256 := word6 + v18
  let v20 : UInt256 := word6 + v6
  let v21 : UInt256 := word13 * word15
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := word5 * word8
  let v24 : UInt256 := v23 + v22
  let v25 : UInt256 := MachineState.readWord s.memory 192
  let v26 : UInt256 := v25 * word12
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := MachineState.readWord s.memory 0
  let v29 : UInt256 := v28 * word9
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := MachineState.readWord s.memory 224
  let v32 : UInt256 := v31 * word19
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := MachineState.readWord s.memory 1216
  let v35 : UInt256 := v34 * word7
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 1248
  let v38 : UInt256 := v37 * word16
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := UInt256.mulMod word13 word15 word14
  let v41 : UInt256 := v40 + v19
  let v42 : UInt256 := UInt256.mulMod word5 word8 word14
  let v43 : UInt256 := v42 + v41
  let v44 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word5.toNat 32) 1088
  let v45 : UInt256 := MachineState.readWord v44 192
  let v46 : UInt256 := UInt256.mulMod v45 word12 word14
  let v47 : UInt256 := v46 + v43
  let v48 : UInt256 := MachineState.readWord v44 0
  let v49 : UInt256 := UInt256.mulMod v48 word9 word14
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord v44 224
  let v52 : UInt256 := UInt256.mulMod v51 word19 word14
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := MachineState.readWord v44 1216
  let v55 : UInt256 := UInt256.mulMod v54 word7 word14
  let v56 : UInt256 := v55 + v53
  {s with pc := UInt256.ofNat 6921, memory := v44, stack := word16 :: word14 :: v56 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest}

theorem squareColumn5_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 word20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5Program {s with pc := UInt256.ofNat 6793, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} =
      some (squareColumn5Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 word20 rest) := by
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := MachineState.readWord s.memory 64
  let v3 : UInt256 := MachineState.readWord s.memory 32
  let v4 : UInt256 := v3 * v2
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := v5 + v5
  let v7 : UInt256 := UInt256.mulMod word4 word2 word3
  let v8 : UInt256 := MachineState.readWord s.memory 128
  let v9 : UInt256 := UInt256.mulMod word10 v8 word14
  let v10 : UInt256 := v9 + v7
  let v11 : UInt256 := MachineState.readWord s.memory 96
  let v12 : UInt256 := UInt256.mulMod word11 v11 word14
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := MachineState.readWord s.memory 64
  let v15 : UInt256 := MachineState.readWord s.memory 32
  let v16 : UInt256 := UInt256.mulMod v15 v14 word14
  let v17 : UInt256 := v16 + v13
  let v18 : UInt256 := v17 + v17
  let v19 : UInt256 := word6 + v18
  let v20 : UInt256 := word6 + v6
  let v21 : UInt256 := word13 * word15
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := word5 * word8
  let v24 : UInt256 := v23 + v22
  let v25 : UInt256 := MachineState.readWord s.memory 192
  let v26 : UInt256 := v25 * word12
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := MachineState.readWord s.memory 0
  let v29 : UInt256 := v28 * word9
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := MachineState.readWord s.memory 224
  let v32 : UInt256 := v31 * word19
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := MachineState.readWord s.memory 1216
  let v35 : UInt256 := v34 * word7
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 1248
  let v38 : UInt256 := v37 * word16
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := UInt256.mulMod word13 word15 word14
  let v41 : UInt256 := v40 + v19
  let v42 : UInt256 := UInt256.mulMod word5 word8 word14
  let v43 : UInt256 := v42 + v41
  let v44 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded word5.toNat 32) 1088
  let v45 : UInt256 := MachineState.readWord v44 192
  let v46 : UInt256 := UInt256.mulMod v45 word12 word14
  let v47 : UInt256 := v46 + v43
  let v48 : UInt256 := MachineState.readWord v44 0
  let v49 : UInt256 := UInt256.mulMod v48 word9 word14
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord v44 224
  let v52 : UInt256 := UInt256.mulMod v51 word19 word14
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := MachineState.readWord v44 1216
  let v55 : UInt256 := UInt256.mulMod v54 word7 word14
  let v56 : UInt256 := v55 + v53
  have h0 : runInstructions squareColumn5part0Program {s with pc := UInt256.ofNat 6793, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6803, memory := s.memory, stack := v5 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part0Model, v0, v1, v2, v3, v4, v5] using squareColumn5part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h1 : runInstructions squareColumn5part1Program {s with pc := UInt256.ofNat 6803, memory := s.memory, stack := v5 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6812, memory := s.memory, stack := word10 :: v8 :: word14 :: v7 :: v6 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part1Model, v6, v7, v8] using squareColumn5part1_run (s) (v5) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h2 : runInstructions squareColumn5part2Program {s with pc := UInt256.ofNat 6812, memory := s.memory, stack := word10 :: v8 :: word14 :: v7 :: v6 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6821, memory := s.memory, stack := v13 :: v6 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part2Model, v9, v10, v11, v12, v13] using squareColumn5part2_run (s) (word10) (v8) (word14) (v7) (v6) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h3 : runInstructions squareColumn5part3Program {s with pc := UInt256.ofNat 6821, memory := s.memory, stack := v13 :: v6 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6831, memory := s.memory, stack := v17 :: v17 :: v6 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part3Model, v14, v15, v16, v17] using squareColumn5part3_run (s) (v13) (v6) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h4 : runInstructions squareColumn5part4Program {s with pc := UInt256.ofNat 6831, memory := s.memory, stack := v17 :: v17 :: v6 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6839, memory := s.memory, stack := v21 :: v20 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part4Model, v18, v19, v20, v21] using squareColumn5part4_run (s) (v17) (v17) (v6) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h5 : runInstructions squareColumn5part5Program {s with pc := UInt256.ofNat 6839, memory := s.memory, stack := v21 :: v20 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6848, memory := s.memory, stack := v25 :: word12 :: v24 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part5Model, v22, v23, v24, v25] using squareColumn5part5_run (s) (v21) (v20) (word5) (v19) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h6 : runInstructions squareColumn5part6Program {s with pc := UInt256.ofNat 6848, memory := s.memory, stack := v25 :: word12 :: v24 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6856, memory := s.memory, stack := word19 :: v30 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part6Model, v26, v27, v28, v29, v30] using squareColumn5part6_run (s) (v25) (word12) (v24) (word5) (v19) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h7 : runInstructions squareColumn5part7Program {s with pc := UInt256.ofNat 6856, memory := s.memory, stack := word19 :: v30 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6867, memory := s.memory, stack := v35 :: v33 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part7Model, v31, v32, v33, v34, v35] using squareColumn5part7_run (s) (word19) (v30) (word5) (v19) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h8 : runInstructions squareColumn5part8Program {s with pc := UInt256.ofNat 6867, memory := s.memory, stack := v35 :: v33 :: word5 :: v19 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6877, memory := s.memory, stack := word14 :: v19 :: word5 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part8Model, v36, v37, v38, v39] using squareColumn5part8_run (s) (v35) (v33) (word5) (v19) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h9 : runInstructions squareColumn5part9Program {s with pc := UInt256.ofNat 6877, memory := s.memory, stack := word14 :: v19 :: word5 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6885, memory := s.memory, stack := v42 :: v41 :: word5 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part9Model, v40, v41, v42] using squareColumn5part9_run (s) (word14) (v19) (word5) (v39) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h10 : runInstructions squareColumn5part10Program {s with pc := UInt256.ofNat 6885, memory := s.memory, stack := v42 :: v41 :: word5 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6896, memory := v44, stack := v45 :: word12 :: word14 :: v43 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part10Model, v43, v44, v45] using squareColumn5part10_run (s) (v42) (v41) (word5) (v39) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h11 : runInstructions squareColumn5part11Program {s with pc := UInt256.ofNat 6896, memory := v44, stack := v45 :: word12 :: word14 :: v43 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6904, memory := v44, stack := v50 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part11Model, v46, v47, v48, v49, v50] using squareColumn5part11_run ({s with memory := v44}) (v45) (word12) (word14) (v43) (v39) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h12 : runInstructions squareColumn5part12Program {s with pc := UInt256.ofNat 6904, memory := v44, stack := v50 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6913, memory := v44, stack := word7 :: word14 :: v53 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part12Model, v51, v52, v53] using squareColumn5part12_run ({s with memory := v44}) (v50) (v39) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  have h13 : runInstructions squareColumn5part13Program {s with pc := UInt256.ofNat 6913, memory := v44, stack := word7 :: word14 :: v53 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} = some {s with pc := UInt256.ofNat 6921, memory := v44, stack := word16 :: word14 :: v56 :: v39 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: word20 :: rest} := by
    simpa only [squareColumn5part13Model, v54, v55, v56] using squareColumn5part13_run ({s with memory := v44}) (word7) (word14) (v53) (v39) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) (word20) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution
