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

def squareColumn6part0Program : List Instr :=
  [.push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD]

def squareColumn6part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := UInt256.mulMod v0 x0 x1
  let v2 : UInt256 := v1 + x2
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  {s with pc := UInt256.ofNat 6475, memory := s.memory, stack := v3 :: x15 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn6part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part0Program {s with pc := UInt256.ofNat 6463, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn6part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part0Program, squareColumn6part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248, ha2720, hf2720]


def squareColumn6part1Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1280,
   .op .MSTORE]

def squareColumn6part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x0
  let v1 : UInt256 := UInt256.land x15 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1280
  {s with pc := UInt256.ofNat 6485, memory := v2, stack := v1 :: x1 :: x2 :: x3 :: x2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn6part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part1Program {s with pc := UInt256.ofNat 6475, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn6part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part1Program, squareColumn6part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def squareColumn6part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD]

def squareColumn6part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x4
  let v3 : UInt256 := MachineState.readWord s.memory 768
  {s with pc := UInt256.ofNat 6497, memory := s.memory, stack := v3 :: x12 :: x18 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn6part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part2Program {s with pc := UInt256.ofNat 6485, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn6part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part2Program, squareColumn6part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]


def squareColumn6part3Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def squareColumn6part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x0
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := v1 * x7
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 6506, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn6part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part3Program {s with pc := UInt256.ofNat 6497, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn6part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part3Program, squareColumn6part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def squareColumn6part4Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]

def squareColumn6part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := x9 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 6518, memory := s.memory, stack := v4 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn6part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part4Program {s with pc := UInt256.ofNat 6506, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn6part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part4Program, squareColumn6part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha96, hf96, ha128, hf128]


def squareColumn6part5Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def squareColumn6part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod x5 x3 x4
  let v4 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 6528, memory := s.memory, stack := v4 :: x14 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem squareColumn6part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part5Program {s with pc := UInt256.ofNat 6518, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (squareColumn6part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part5Program, squareColumn6part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def squareColumn6part6Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD]

def squareColumn6part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 128
  let v3 : UInt256 := UInt256.mulMod x9 v2 x12
  {s with pc := UInt256.ofNat 6537, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn6part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part6Program {s with pc := UInt256.ofNat 6528, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn6part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part6Program, squareColumn6part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def squareColumn6part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def squareColumn6part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 96
  let v2 : UInt256 := MachineState.readWord s.memory 32
  let v3 : UInt256 := UInt256.mulMod v2 v1 x11
  let v4 : UInt256 := v3 + v0
  {s with pc := UInt256.ofNat 6547, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn6part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part7Program {s with pc := UInt256.ofNat 6537, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn6part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part7Program, squareColumn6part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha96, hf96]


def squareColumn6part8Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD]

def squareColumn6part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := x2 + v0
  let v2 : UInt256 := x2 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 6556, memory := s.memory, stack := v3 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn6part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part8Program {s with pc := UInt256.ofNat 6547, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn6part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part8Program, squareColumn6part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]


def squareColumn6part9Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨2, by decide⟩)]

def squareColumn6part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1600
  {s with pc := UInt256.ofNat 6566, memory := s.memory, stack := x2 :: x11 :: v1 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v2 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn6part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part9Program {s with pc := UInt256.ofNat 6556, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn6part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1600 : (1600 : UInt256).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part9Program, squareColumn6part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1600, hf1600]


def squareColumn6part10Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD]

def squareColumn6part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x3 x1 x11
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x3 * x1
  let v3 : UInt256 := v2 + x2
  {s with pc := UInt256.ofNat 6574, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn6part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part10Program {s with pc := UInt256.ofNat 6566, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn6part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn6part10Program, squareColumn6part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn6part11Program : List Instr :=
  [.push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def squareColumn6part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1088
  let v1 : UInt256 := x8 * v0
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 192
  {s with pc := UInt256.ofNat 6585, memory := s.memory, stack := v3 :: x3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn6part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part11Program {s with pc := UInt256.ofNat 6574, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn6part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part11Program, squareColumn6part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192, ha1088, hf1088]


def squareColumn6part12Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]

def squareColumn6part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := v2 * x9
  {s with pc := UInt256.ofNat 6591, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn6part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6part12Program {s with pc := UInt256.ofNat 6585, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn6part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn6part12Program, squareColumn6part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def squareColumn6Program : List Instr :=
  [.push 2 1248,
   .op .MLOAD,
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
   .push 2 1280,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]

def squareColumn6Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := UInt256.mulMod v0 carry word0
  let v2 : UInt256 := v1 + word1
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  let v4 : UInt256 := word2 * v3
  let v5 : UInt256 := UInt256.land word13 v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 1280
  let v7 : UInt256 := UInt256.mulMod v5 word14 word10
  let v8 : UInt256 := v7 + v2
  let v9 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v8 word10
  let v10 : UInt256 := MachineState.readWord v6 768
  let v11 : UInt256 := word16 * v10
  let v12 : UInt256 := MachineState.readWord v6 160
  let v13 : UInt256 := v12 * word6
  let v14 : UInt256 := v13 + v11
  let v15 : UInt256 := MachineState.readWord v6 128
  let v16 : UInt256 := word7 * v15
  let v17 : UInt256 := v16 + v14
  let v18 : UInt256 := MachineState.readWord v6 96
  let v19 : UInt256 := MachineState.readWord v6 32
  let v20 : UInt256 := v19 * v18
  let v21 : UInt256 := v20 + v17
  let v22 : UInt256 := v21 + v21
  let v23 : UInt256 := UInt256.mulMod word16 v10 word10
  let v24 : UInt256 := MachineState.readWord v6 160
  let v25 : UInt256 := UInt256.mulMod word6 v24 word10
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := MachineState.readWord v6 128
  let v28 : UInt256 := UInt256.mulMod word7 v27 word10
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord v6 96
  let v31 : UInt256 := MachineState.readWord v6 32
  let v32 : UInt256 := UInt256.mulMod v31 v30 word10
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := v33 + v33
  let v35 : UInt256 := v9 + v34
  let v36 : UInt256 := v9 + v22
  let v37 : UInt256 := MachineState.readWord v6 64
  let v38 : UInt256 := v37 * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := MachineState.readWord v6 1600
  let v41 : UInt256 := UInt256.mulMod v40 word11 word10
  let v42 : UInt256 := v41 + v35
  let v43 : UInt256 := v40 * word11
  let v44 : UInt256 := v43 + v39
  let v45 : UInt256 := MachineState.readWord v6 1088
  let v46 : UInt256 := word9 * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := MachineState.readWord v6 192
  let v49 : UInt256 := v48 * word4
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord v6 0
  let v52 : UInt256 := v51 * word8
  {s with pc := UInt256.ofNat 6591, memory := v6, stack := v52 :: v50 :: v42 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest}

theorem squareColumn6_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6Program {s with pc := UInt256.ofNat 6463, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} =
      some (squareColumn6Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 1248
  let v1 : UInt256 := UInt256.mulMod v0 carry word0
  let v2 : UInt256 := v1 + word1
  let v3 : UInt256 := MachineState.readWord s.memory 2720
  let v4 : UInt256 := word2 * v3
  let v5 : UInt256 := UInt256.land word13 v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 1280
  let v7 : UInt256 := UInt256.mulMod v5 word14 word10
  let v8 : UInt256 := v7 + v2
  let v9 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v8 word10
  let v10 : UInt256 := MachineState.readWord v6 768
  let v11 : UInt256 := word16 * v10
  let v12 : UInt256 := MachineState.readWord v6 160
  let v13 : UInt256 := v12 * word6
  let v14 : UInt256 := v13 + v11
  let v15 : UInt256 := MachineState.readWord v6 128
  let v16 : UInt256 := word7 * v15
  let v17 : UInt256 := v16 + v14
  let v18 : UInt256 := MachineState.readWord v6 96
  let v19 : UInt256 := MachineState.readWord v6 32
  let v20 : UInt256 := v19 * v18
  let v21 : UInt256 := v20 + v17
  let v22 : UInt256 := v21 + v21
  let v23 : UInt256 := UInt256.mulMod word16 v10 word10
  let v24 : UInt256 := MachineState.readWord v6 160
  let v25 : UInt256 := UInt256.mulMod word6 v24 word10
  let v26 : UInt256 := v25 + v23
  let v27 : UInt256 := MachineState.readWord v6 128
  let v28 : UInt256 := UInt256.mulMod word7 v27 word10
  let v29 : UInt256 := v28 + v26
  let v30 : UInt256 := MachineState.readWord v6 96
  let v31 : UInt256 := MachineState.readWord v6 32
  let v32 : UInt256 := UInt256.mulMod v31 v30 word10
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := v33 + v33
  let v35 : UInt256 := v9 + v34
  let v36 : UInt256 := v9 + v22
  let v37 : UInt256 := MachineState.readWord v6 64
  let v38 : UInt256 := v37 * v37
  let v39 : UInt256 := v38 + v36
  let v40 : UInt256 := MachineState.readWord v6 1600
  let v41 : UInt256 := UInt256.mulMod v40 word11 word10
  let v42 : UInt256 := v41 + v35
  let v43 : UInt256 := v40 * word11
  let v44 : UInt256 := v43 + v39
  let v45 : UInt256 := MachineState.readWord v6 1088
  let v46 : UInt256 := word9 * v45
  let v47 : UInt256 := v46 + v44
  let v48 : UInt256 := MachineState.readWord v6 192
  let v49 : UInt256 := v48 * word4
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord v6 0
  let v52 : UInt256 := v51 * word8
  have h0 : runInstructions squareColumn6part0Program {s with pc := UInt256.ofNat 6463, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6475, memory := s.memory, stack := v3 :: word14 :: word10 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part0Model, v0, v1, v2, v3] using squareColumn6part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h1 : runInstructions squareColumn6part1Program {s with pc := UInt256.ofNat 6475, memory := s.memory, stack := v3 :: word14 :: word10 :: v2 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6485, memory := v6, stack := v5 :: word14 :: word10 :: v2 :: word10 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part1Model, v4, v5, v6] using squareColumn6part1_run (s) (v3) (word14) (word10) (v2) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h2 : runInstructions squareColumn6part2Program {s with pc := UInt256.ofNat 6485, memory := v6, stack := v5 :: word14 :: word10 :: v2 :: word10 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6497, memory := v6, stack := v10 :: word10 :: word16 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part2Model, v7, v8, v9, v10] using squareColumn6part2_run ({s with memory := v6}) (v5) (word14) (word10) (v2) (word10) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h3 : runInstructions squareColumn6part3Program {s with pc := UInt256.ofNat 6497, memory := v6, stack := v10 :: word10 :: word16 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6506, memory := v6, stack := v14 :: v10 :: word10 :: word16 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part3Model, v11, v12, v13, v14] using squareColumn6part3_run ({s with memory := v6}) (v10) (word10) (word16) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h4 : runInstructions squareColumn6part4Program {s with pc := UInt256.ofNat 6506, memory := v6, stack := v14 :: v10 :: word10 :: word16 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6518, memory := v6, stack := v19 :: v18 :: v17 :: v10 :: word10 :: word16 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part4Model, v15, v16, v17, v18, v19] using squareColumn6part4_run ({s with memory := v6}) (v14) (v10) (word10) (word16) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h5 : runInstructions squareColumn6part5Program {s with pc := UInt256.ofNat 6518, memory := v6, stack := v19 :: v18 :: v17 :: v10 :: word10 :: word16 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6528, memory := v6, stack := v24 :: word10 :: v23 :: v22 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part5Model, v20, v21, v22, v23, v24] using squareColumn6part5_run ({s with memory := v6}) (v19) (v18) (v17) (v10) (word10) (word16) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h6 : runInstructions squareColumn6part6Program {s with pc := UInt256.ofNat 6528, memory := v6, stack := v24 :: word10 :: v23 :: v22 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6537, memory := v6, stack := v28 :: v26 :: v22 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part6Model, v25, v26, v27, v28] using squareColumn6part6_run ({s with memory := v6}) (v24) (word10) (v23) (v22) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h7 : runInstructions squareColumn6part7Program {s with pc := UInt256.ofNat 6537, memory := v6, stack := v28 :: v26 :: v22 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6547, memory := v6, stack := v33 :: v22 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part7Model, v29, v30, v31, v32, v33] using squareColumn6part7_run ({s with memory := v6}) (v28) (v26) (v22) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h8 : runInstructions squareColumn6part8Program {s with pc := UInt256.ofNat 6547, memory := v6, stack := v33 :: v22 :: v9 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6556, memory := v6, stack := v37 :: v36 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part8Model, v34, v35, v36, v37] using squareColumn6part8_run ({s with memory := v6}) (v33) (v22) (v9) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h9 : runInstructions squareColumn6part9Program {s with pc := UInt256.ofNat 6556, memory := v6, stack := v37 :: v36 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6566, memory := v6, stack := v35 :: word11 :: v39 :: v40 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part9Model, v38, v39, v40] using squareColumn6part9_run ({s with memory := v6}) (v37) (v36) (v35) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h10 : runInstructions squareColumn6part10Program {s with pc := UInt256.ofNat 6566, memory := v6, stack := v35 :: word11 :: v39 :: v40 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6574, memory := v6, stack := v44 :: v42 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part10Model, v41, v42, v43, v44] using squareColumn6part10_run ({s with memory := v6}) (v35) (word11) (v39) (v40) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (v40) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h11 : runInstructions squareColumn6part11Program {s with pc := UInt256.ofNat 6574, memory := v6, stack := v44 :: v42 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6585, memory := v6, stack := v48 :: word4 :: v47 :: v42 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part11Model, v45, v46, v47, v48] using squareColumn6part11_run ({s with memory := v6}) (v44) (v42) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (v40) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h12 : runInstructions squareColumn6part12Program {s with pc := UInt256.ofNat 6585, memory := v6, stack := v48 :: word4 :: v47 :: v42 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 6591, memory := v6, stack := v52 :: v50 :: v42 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: v40 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn6part12Model, v49, v50, v51, v52] using squareColumn6part12_run ({s with memory := v6}) (v48) (word4) (v47) (v42) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (v40) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
