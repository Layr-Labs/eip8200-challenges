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

def squareColumn8part0Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD]

def squareColumn8part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 7188, memory := s.memory, stack := v4 :: v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn8part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part0Program {s with pc := UInt256.ofNat 7177, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn8part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part0Program, squareColumn8part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha64, hf64, ha96, hf96]


def squareColumn8part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def squareColumn8part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod x5 x3 x4
  let v4 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 7198, memory := s.memory, stack := v4 :: x14 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem squareColumn8part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part1Program {s with pc := UInt256.ofNat 7188, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (squareColumn8part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part1Program, squareColumn8part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def squareColumn8part2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]

def squareColumn8part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x9 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 128
  let v3 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 7208, memory := s.memory, stack := v3 :: v2 :: x12 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn8part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part2Program {s with pc := UInt256.ofNat 7198, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn8part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part2Program, squareColumn8part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha128, hf128]


def squareColumn8part3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD]

def squareColumn8part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := UInt256.mulMod v3 v2 x13
  {s with pc := UInt256.ofNat 7218, memory := s.memory, stack := v4 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn8part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part3Program {s with pc := UInt256.ofNat 7208, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn8part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part3Program, squareColumn8part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha96, hf96]


def squareColumn8part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 1088,
   .op .MLOAD]

def squareColumn8part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + v0
  let v2 : UInt256 := x3 + v1
  let v3 : UInt256 := x3 + x2
  let v4 : UInt256 := MachineState.readWord s.memory 1088
  {s with pc := UInt256.ofNat 7229, memory := s.memory, stack := v4 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn8part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part4Program {s with pc := UInt256.ofNat 7218, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn8part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part4Program, squareColumn8part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def squareColumn8part5Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def squareColumn8part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x11 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := x9 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7238, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn8part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part5Program {s with pc := UInt256.ofNat 7229, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn8part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part5Program, squareColumn8part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def squareColumn8part6Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def squareColumn8part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 0
  let v1 : UInt256 := v0 * x3
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 224
  {s with pc := UInt256.ofNat 7247, memory := s.memory, stack := v3 :: x7 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn8part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part6Program {s with pc := UInt256.ofNat 7238, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn8part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part6Program, squareColumn8part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]


def squareColumn8part7Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def squareColumn8part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  let v3 : UInt256 := v2 * x6
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7257, memory := s.memory, stack := x16 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn8part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part7Program {s with pc := UInt256.ofNat 7247, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn8part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part7Program, squareColumn8part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def squareColumn8part8Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def squareColumn8part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x6 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 1280
  let v3 : UInt256 := v2 * x3
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7267, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn8part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part8Program {s with pc := UInt256.ofNat 7257, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn8part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part8Program, squareColumn8part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def squareColumn8part9Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD]

def squareColumn8part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x13 * x11
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 1088
  {s with pc := UInt256.ofNat 7277, memory := s.memory, stack := v2 :: x9 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn8part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part9Program {s with pc := UInt256.ofNat 7267, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn8part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : UInt256).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part9Program, squareColumn8part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def squareColumn8part10Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def squareColumn8part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x12 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 192
  let v3 : UInt256 := UInt256.mulMod x10 v2 x11
  {s with pc := UInt256.ofNat 7286, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn8part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part10Program {s with pc := UInt256.ofNat 7277, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn8part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part10Program, squareColumn8part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def squareColumn8part11Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn8part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.mulMod v1 x4 x10
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 7294, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn8part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part11Program {s with pc := UInt256.ofNat 7286, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn8part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part11Program, squareColumn8part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def squareColumn8part12Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def squareColumn8part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.mulMod v0 x8 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 7306, memory := s.memory, stack := v3 :: x5 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn8part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8part12Program {s with pc := UInt256.ofNat 7294, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn8part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn8part12Program, squareColumn8part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


def squareColumn8Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
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
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def squareColumn8Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := v0 * carry
  let v2 : UInt256 := v1 + word0
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := MachineState.readWord s.memory 64
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod word3 word1 word2
  let v9 : UInt256 := MachineState.readWord s.memory 160
  let v10 : UInt256 := UInt256.mulMod word9 v9 word12
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := MachineState.readWord s.memory 128
  let v13 : UInt256 := MachineState.readWord s.memory 32
  let v14 : UInt256 := UInt256.mulMod v13 v12 word12
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := MachineState.readWord s.memory 96
  let v17 : UInt256 := MachineState.readWord s.memory 64
  let v18 : UInt256 := UInt256.mulMod v17 v16 word12
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := word4 + v20
  let v22 : UInt256 := word4 + v7
  let v23 : UInt256 := MachineState.readWord s.memory 1088
  let v24 : UInt256 := word13 * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 192
  let v27 : UInt256 := word11 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 0
  let v30 : UInt256 := v29 * word6
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := MachineState.readWord s.memory 224
  let v33 : UInt256 := v32 * word10
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 1216
  let v36 : UInt256 := v35 * word7
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := word8 * word17
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := MachineState.readWord s.memory 1280
  let v41 : UInt256 := v40 * word5
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := word16 * word14
  let v44 : UInt256 := v43 + v42
  let v45 : UInt256 := MachineState.readWord s.memory 1088
  let v46 : UInt256 := UInt256.mulMod word13 v45 word12
  let v47 : UInt256 := v46 + v21
  let v48 : UInt256 := MachineState.readWord s.memory 192
  let v49 : UInt256 := UInt256.mulMod word11 v48 word12
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord s.memory 0
  let v52 : UInt256 := UInt256.mulMod v51 word6 word12
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := MachineState.readWord s.memory 224
  let v55 : UInt256 := UInt256.mulMod v54 word10 word12
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 7306, memory := s.memory, stack := v57 :: word7 :: word12 :: v56 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest}

theorem squareColumn8_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8Program {s with pc := UInt256.ofNat 7177, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} =
      some (squareColumn8Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := v0 * carry
  let v2 : UInt256 := v1 + word0
  let v3 : UInt256 := MachineState.readWord s.memory 96
  let v4 : UInt256 := MachineState.readWord s.memory 64
  let v5 : UInt256 := v4 * v3
  let v6 : UInt256 := v5 + v2
  let v7 : UInt256 := v6 + v6
  let v8 : UInt256 := UInt256.mulMod word3 word1 word2
  let v9 : UInt256 := MachineState.readWord s.memory 160
  let v10 : UInt256 := UInt256.mulMod word9 v9 word12
  let v11 : UInt256 := v10 + v8
  let v12 : UInt256 := MachineState.readWord s.memory 128
  let v13 : UInt256 := MachineState.readWord s.memory 32
  let v14 : UInt256 := UInt256.mulMod v13 v12 word12
  let v15 : UInt256 := v14 + v11
  let v16 : UInt256 := MachineState.readWord s.memory 96
  let v17 : UInt256 := MachineState.readWord s.memory 64
  let v18 : UInt256 := UInt256.mulMod v17 v16 word12
  let v19 : UInt256 := v18 + v15
  let v20 : UInt256 := v19 + v19
  let v21 : UInt256 := word4 + v20
  let v22 : UInt256 := word4 + v7
  let v23 : UInt256 := MachineState.readWord s.memory 1088
  let v24 : UInt256 := word13 * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := MachineState.readWord s.memory 192
  let v27 : UInt256 := word11 * v26
  let v28 : UInt256 := v27 + v25
  let v29 : UInt256 := MachineState.readWord s.memory 0
  let v30 : UInt256 := v29 * word6
  let v31 : UInt256 := v30 + v28
  let v32 : UInt256 := MachineState.readWord s.memory 224
  let v33 : UInt256 := v32 * word10
  let v34 : UInt256 := v33 + v31
  let v35 : UInt256 := MachineState.readWord s.memory 1216
  let v36 : UInt256 := v35 * word7
  let v37 : UInt256 := v36 + v34
  let v38 : UInt256 := word8 * word17
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := MachineState.readWord s.memory 1280
  let v41 : UInt256 := v40 * word5
  let v42 : UInt256 := v41 + v39
  let v43 : UInt256 := word16 * word14
  let v44 : UInt256 := v43 + v42
  let v45 : UInt256 := MachineState.readWord s.memory 1088
  let v46 : UInt256 := UInt256.mulMod word13 v45 word12
  let v47 : UInt256 := v46 + v21
  let v48 : UInt256 := MachineState.readWord s.memory 192
  let v49 : UInt256 := UInt256.mulMod word11 v48 word12
  let v50 : UInt256 := v49 + v47
  let v51 : UInt256 := MachineState.readWord s.memory 0
  let v52 : UInt256 := UInt256.mulMod v51 word6 word12
  let v53 : UInt256 := v52 + v50
  let v54 : UInt256 := MachineState.readWord s.memory 224
  let v55 : UInt256 := UInt256.mulMod v54 word10 word12
  let v56 : UInt256 := v55 + v53
  let v57 : UInt256 := MachineState.readWord s.memory 1216
  have h0 : runInstructions squareColumn8part0Program {s with pc := UInt256.ofNat 7177, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7188, memory := s.memory, stack := v4 :: v3 :: v2 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part0Model, v0, v1, v2, v3, v4] using squareColumn8part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h1 : runInstructions squareColumn8part1Program {s with pc := UInt256.ofNat 7188, memory := s.memory, stack := v4 :: v3 :: v2 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7198, memory := s.memory, stack := v9 :: word12 :: v8 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part1Model, v5, v6, v7, v8, v9] using squareColumn8part1_run (s) (v4) (v3) (v2) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h2 : runInstructions squareColumn8part2Program {s with pc := UInt256.ofNat 7198, memory := s.memory, stack := v9 :: word12 :: v8 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7208, memory := s.memory, stack := v13 :: v12 :: word12 :: v11 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part2Model, v10, v11, v12, v13] using squareColumn8part2_run (s) (v9) (word12) (v8) (v7) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h3 : runInstructions squareColumn8part3Program {s with pc := UInt256.ofNat 7208, memory := s.memory, stack := v13 :: v12 :: word12 :: v11 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7218, memory := s.memory, stack := v18 :: v15 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part3Model, v14, v15, v16, v17, v18] using squareColumn8part3_run (s) (v13) (v12) (word12) (v11) (v7) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h4 : runInstructions squareColumn8part4Program {s with pc := UInt256.ofNat 7218, memory := s.memory, stack := v18 :: v15 :: v7 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7229, memory := s.memory, stack := v23 :: v22 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part4Model, v19, v20, v21, v22, v23] using squareColumn8part4_run (s) (v18) (v15) (v7) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h5 : runInstructions squareColumn8part5Program {s with pc := UInt256.ofNat 7229, memory := s.memory, stack := v23 :: v22 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7238, memory := s.memory, stack := v28 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part5Model, v24, v25, v26, v27, v28] using squareColumn8part5_run (s) (v23) (v22) (v21) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h6 : runInstructions squareColumn8part6Program {s with pc := UInt256.ofNat 7238, memory := s.memory, stack := v28 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7247, memory := s.memory, stack := v32 :: word10 :: v31 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part6Model, v29, v30, v31, v32] using squareColumn8part6_run (s) (v28) (v21) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h7 : runInstructions squareColumn8part7Program {s with pc := UInt256.ofNat 7247, memory := s.memory, stack := v32 :: word10 :: v31 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7257, memory := s.memory, stack := word17 :: v37 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part7Model, v33, v34, v35, v36, v37] using squareColumn8part7_run (s) (v32) (word10) (v31) (v21) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h8 : runInstructions squareColumn8part8Program {s with pc := UInt256.ofNat 7257, memory := s.memory, stack := word17 :: v37 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7267, memory := s.memory, stack := v42 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part8Model, v38, v39, v40, v41, v42] using squareColumn8part8_run (s) (word17) (v37) (v21) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h9 : runInstructions squareColumn8part9Program {s with pc := UInt256.ofNat 7267, memory := s.memory, stack := v42 :: v21 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7277, memory := s.memory, stack := v45 :: word12 :: v21 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part9Model, v43, v44, v45] using squareColumn8part9_run (s) (v42) (v21) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h10 : runInstructions squareColumn8part10Program {s with pc := UInt256.ofNat 7277, memory := s.memory, stack := v45 :: word12 :: v21 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7286, memory := s.memory, stack := v49 :: v47 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part10Model, v46, v47, v48, v49] using squareColumn8part10_run (s) (v45) (word12) (v21) (v44) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h11 : runInstructions squareColumn8part11Program {s with pc := UInt256.ofNat 7286, memory := s.memory, stack := v49 :: v47 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7294, memory := s.memory, stack := word12 :: v53 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part11Model, v50, v51, v52, v53] using squareColumn8part11_run (s) (v49) (v47) (v44) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  have h12 : runInstructions squareColumn8part12Program {s with pc := UInt256.ofNat 7294, memory := s.memory, stack := word12 :: v53 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} = some {s with pc := UInt256.ofNat 7306, memory := s.memory, stack := v57 :: word7 :: word12 :: v56 :: v44 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: rest} := by
    simpa only [squareColumn8part12Model, v54, v55, v56, v57] using squareColumn8part12_run (s) (word12) (v53) (v44) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
