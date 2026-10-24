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

def squareColumn7part0Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def squareColumn7part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := v1 * x5
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 7061, memory := s.memory, stack := v4 :: x15 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn7part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part0Program {s with pc := UInt256.ofNat 7049, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn7part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part0Program, squareColumn7part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


def squareColumn7part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩)]

def squareColumn7part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := v2 * x4
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7071, memory := s.memory, stack := x13 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn7part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part1Program {s with pc := UInt256.ofNat 7061, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn7part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part1Program, squareColumn7part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def squareColumn7part2Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD]

def squareColumn7part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 7082, memory := s.memory, stack := v3 :: x10 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn7part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part2Program {s with pc := UInt256.ofNat 7071, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn7part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part2Program, squareColumn7part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha1280, hf1280]


def squareColumn7part3Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def squareColumn7part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  let v3 : UInt256 := UInt256.mulMod x10 v2 x11
  {s with pc := UInt256.ofNat 7092, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn7part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part3Program {s with pc := UInt256.ofNat 7082, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn7part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part3Program, squareColumn7part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def squareColumn7part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn7part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 192
  let v2 : UInt256 := UInt256.mulMod v1 x4 x10
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 7101, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn7part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part4Program {s with pc := UInt256.ofNat 7092, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn7part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part4Program, squareColumn7part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def squareColumn7part5Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def squareColumn7part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := UInt256.mulMod v0 x8 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 7111, memory := s.memory, stack := v3 :: x5 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn7part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part5Program {s with pc := UInt256.ofNat 7101, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn7part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part5Program, squareColumn7part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]


def squareColumn7part6Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def squareColumn7part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := UInt256.mulMod v2 x17 x12
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7121, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn7part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part6Program {s with pc := UInt256.ofNat 7111, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn7part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part6Program, squareColumn7part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def squareColumn7part7Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩)]

def squareColumn7part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := UInt256.mulMod v0 x2 x9
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 7131, memory := s.memory, stack := x11 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn7part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part7Program {s with pc := UInt256.ofNat 7121, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn7part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part7Program, squareColumn7part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def squareColumn7part8Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op .MUL]

def squareColumn7part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  let v4 : UInt256 := v3 * x3
  {s with pc := UInt256.ofNat 7143, memory := s.memory, stack := v4 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn7part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part8Program {s with pc := UInt256.ofNat 7131, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn7part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part8Program, squareColumn7part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280, ha2720, hf2720]


def squareColumn7part9Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def squareColumn7part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x13 x0
  let v1 : UInt256 := UInt256.mulMod x14 v0 x10
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 7151, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: v0 :: x15 :: x16 :: rest}

theorem squareColumn7part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part9Program {s with pc := UInt256.ofNat 7143, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn7part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn7part9Program, squareColumn7part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn7part10Program : List Instr :=
  [.push 2 2048,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1248,
   .op .MLOAD]

def squareColumn7part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x9
  let v1 : UInt256 := MachineState.readWord s.memory 1248
  {s with pc := UInt256.ofNat 7164, memory := s.memory, stack := v1 :: x9 :: x15 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn7part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part10Program {s with pc := UInt256.ofNat 7151, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn7part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part10Program, squareColumn7part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def squareColumn7part11Program : List Instr :=
  [.op (.Swap ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL]

def squareColumn7part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x7
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := x8 * v1
  {s with pc := UInt256.ofNat 7173, memory := s.memory, stack := v2 :: v0 :: x7 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn7part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part11Program {s with pc := UInt256.ofNat 7164, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn7part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part11Program, squareColumn7part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def squareColumn7part12Program : List Instr :=
  [.op .ADD,
   .push 1 128,
   .op .MLOAD]

def squareColumn7part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 7177, memory := s.memory, stack := v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn7part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7part12Program {s with pc := UInt256.ofNat 7173, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn7part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn7part12Program, squareColumn7part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def squareColumn7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op .POP,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def squareColumn7Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := v1 * word4
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 1216
  let v5 : UInt256 := v4 * word14
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := MachineState.readWord s.memory 1248
  let v8 : UInt256 := v7 * word2
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := MachineState.readWord s.memory 1280
  let v11 : UInt256 := v10 * word11
  let v12 : UInt256 := v11 + v9
  let v13 : UInt256 := MachineState.readWord s.memory 64
  let v14 : UInt256 := UInt256.mulMod v13 v13 word9
  let v15 : UInt256 := v14 + word1
  let v16 : UInt256 := MachineState.readWord s.memory 1088
  let v17 : UInt256 := UInt256.mulMod word8 v16 word9
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := MachineState.readWord s.memory 192
  let v20 : UInt256 := UInt256.mulMod v19 word3 word9
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 0
  let v23 : UInt256 := UInt256.mulMod v22 word7 word9
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord s.memory 224
  let v26 : UInt256 := UInt256.mulMod v25 word4 word9
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := MachineState.readWord s.memory 1216
  let v29 : UInt256 := UInt256.mulMod v28 word14 word9
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := MachineState.readWord s.memory 1248
  let v32 : UInt256 := UInt256.mulMod v31 word2 word9
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := MachineState.readWord s.memory 1280
  let v35 : UInt256 := UInt256.mulMod v34 word11 word9
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 2720
  let v38 : UInt256 := v37 * v12
  let v39 : UInt256 := UInt256.land word12 v38
  let v40 : UInt256 := UInt256.mulMod word13 v39 word9
  let v41 : UInt256 := v40 + v36
  let v42 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v41 word9
  let v43 : UInt256 := MachineState.readWord s.memory 1248
  let v44 : UInt256 := word15 * word5
  let v45 : UInt256 := MachineState.readWord s.memory 160
  let v46 : UInt256 := word6 * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 7177, memory := s.memory, stack := v48 :: v47 :: word5 :: word9 :: word15 :: v42 :: word2 :: word3 :: word4 :: v43 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest}

theorem squareColumn7_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7Program {s with pc := UInt256.ofNat 7049, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} =
      some (squareColumn7Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 rest) := by
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := v1 * word4
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 1216
  let v5 : UInt256 := v4 * word14
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := MachineState.readWord s.memory 1248
  let v8 : UInt256 := v7 * word2
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := MachineState.readWord s.memory 1280
  let v11 : UInt256 := v10 * word11
  let v12 : UInt256 := v11 + v9
  let v13 : UInt256 := MachineState.readWord s.memory 64
  let v14 : UInt256 := UInt256.mulMod v13 v13 word9
  let v15 : UInt256 := v14 + word1
  let v16 : UInt256 := MachineState.readWord s.memory 1088
  let v17 : UInt256 := UInt256.mulMod word8 v16 word9
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := MachineState.readWord s.memory 192
  let v20 : UInt256 := UInt256.mulMod v19 word3 word9
  let v21 : UInt256 := v20 + v18
  let v22 : UInt256 := MachineState.readWord s.memory 0
  let v23 : UInt256 := UInt256.mulMod v22 word7 word9
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord s.memory 224
  let v26 : UInt256 := UInt256.mulMod v25 word4 word9
  let v27 : UInt256 := v26 + v24
  let v28 : UInt256 := MachineState.readWord s.memory 1216
  let v29 : UInt256 := UInt256.mulMod v28 word14 word9
  let v30 : UInt256 := v29 + v27
  let v31 : UInt256 := MachineState.readWord s.memory 1248
  let v32 : UInt256 := UInt256.mulMod v31 word2 word9
  let v33 : UInt256 := v32 + v30
  let v34 : UInt256 := MachineState.readWord s.memory 1280
  let v35 : UInt256 := UInt256.mulMod v34 word11 word9
  let v36 : UInt256 := v35 + v33
  let v37 : UInt256 := MachineState.readWord s.memory 2720
  let v38 : UInt256 := v37 * v12
  let v39 : UInt256 := UInt256.land word12 v38
  let v40 : UInt256 := UInt256.mulMod word13 v39 word9
  let v41 : UInt256 := v40 + v36
  let v42 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v41 word9
  let v43 : UInt256 := MachineState.readWord s.memory 1248
  let v44 : UInt256 := word15 * word5
  let v45 : UInt256 := MachineState.readWord s.memory 160
  let v46 : UInt256 := word6 * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := MachineState.readWord s.memory 128
  have h0 : runInstructions squareColumn7part0Program {s with pc := UInt256.ofNat 7049, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7061, memory := s.memory, stack := v4 :: word14 :: v3 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part0Model, v0, v1, v2, v3, v4] using squareColumn7part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h1 : runInstructions squareColumn7part1Program {s with pc := UInt256.ofNat 7061, memory := s.memory, stack := v4 :: word14 :: v3 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7071, memory := s.memory, stack := word11 :: v9 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part1Model, v5, v6, v7, v8, v9] using squareColumn7part1_run (s) (v4) (word14) (v3) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h2 : runInstructions squareColumn7part2Program {s with pc := UInt256.ofNat 7071, memory := s.memory, stack := word11 :: v9 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7082, memory := s.memory, stack := v13 :: word9 :: word1 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part2Model, v10, v11, v12, v13] using squareColumn7part2_run (s) (word11) (v9) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h3 : runInstructions squareColumn7part3Program {s with pc := UInt256.ofNat 7082, memory := s.memory, stack := v13 :: word9 :: word1 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7092, memory := s.memory, stack := v17 :: v15 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part3Model, v14, v15, v16, v17] using squareColumn7part3_run (s) (v13) (word9) (word1) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h4 : runInstructions squareColumn7part4Program {s with pc := UInt256.ofNat 7092, memory := s.memory, stack := v17 :: v15 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7101, memory := s.memory, stack := word9 :: v21 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part4Model, v18, v19, v20, v21] using squareColumn7part4_run (s) (v17) (v15) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h5 : runInstructions squareColumn7part5Program {s with pc := UInt256.ofNat 7101, memory := s.memory, stack := word9 :: v21 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7111, memory := s.memory, stack := v25 :: word4 :: word9 :: v24 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part5Model, v22, v23, v24, v25] using squareColumn7part5_run (s) (word9) (v21) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h6 : runInstructions squareColumn7part6Program {s with pc := UInt256.ofNat 7111, memory := s.memory, stack := v25 :: word4 :: word9 :: v24 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7121, memory := s.memory, stack := v30 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part6Model, v26, v27, v28, v29, v30] using squareColumn7part6_run (s) (v25) (word4) (word9) (v24) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h7 : runInstructions squareColumn7part7Program {s with pc := UInt256.ofNat 7121, memory := s.memory, stack := v30 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7131, memory := s.memory, stack := word11 :: word9 :: v33 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part7Model, v31, v32, v33] using squareColumn7part7_run (s) (v30) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h8 : runInstructions squareColumn7part8Program {s with pc := UInt256.ofNat 7131, memory := s.memory, stack := word11 :: word9 :: v33 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7143, memory := s.memory, stack := v38 :: v36 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part8Model, v34, v35, v36, v37, v38] using squareColumn7part8_run (s) (word11) (word9) (v33) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h9 : runInstructions squareColumn7part9Program {s with pc := UInt256.ofNat 7143, memory := s.memory, stack := v38 :: v36 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7151, memory := s.memory, stack := v41 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part9Model, v39, v40, v41] using squareColumn7part9_run (s) (v38) (v36) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h10 : runInstructions squareColumn7part10Program {s with pc := UInt256.ofNat 7151, memory := s.memory, stack := v41 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7164, memory := s.memory, stack := v43 :: word9 :: word15 :: v42 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part10Model, v42, v43] using squareColumn7part10_run (s) (v41) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v39) (word14) (word15) rest hcap hact
  have h11 : runInstructions squareColumn7part11Program {s with pc := UInt256.ofNat 7164, memory := s.memory, stack := v43 :: word9 :: word15 :: v42 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7173, memory := s.memory, stack := v46 :: v44 :: word5 :: word9 :: word15 :: v42 :: word2 :: word3 :: word4 :: v43 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part11Model, v44, v45, v46] using squareColumn7part11_run (s) (v43) (word9) (word15) (v42) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v39) (word14) (word15) rest hcap hact
  have h12 : runInstructions squareColumn7part12Program {s with pc := UInt256.ofNat 7173, memory := s.memory, stack := v46 :: v44 :: word5 :: word9 :: word15 :: v42 :: word2 :: word3 :: word4 :: v43 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7177, memory := s.memory, stack := v48 :: v47 :: word5 :: word9 :: word15 :: v42 :: word2 :: word3 :: word4 :: v43 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v39 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn7part12Model, v47, v48] using squareColumn7part12_run (s) (v46) (v44) (word5) (word9) (word15) (v42) (word2) (word3) (word4) (v43) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v39) (word14) (word15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
