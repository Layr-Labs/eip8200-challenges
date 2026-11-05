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

local notation "W" => UInt256
local notation "N" => UInt256.ofNat

def sq8p0P : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD]

def sq8p0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := v0 * x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := MachineState.readWord s.memory 64
  {s with pc := N 6747, memory := s.memory, stack := v4 :: v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq8p0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p0P {s with pc := N 6736, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq8p0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p0P, sq8p0M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha64, hf64, ha96, hf96]


def sq8p1P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def sq8p1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := v1 + v1
  let v3 : W := UInt256.mulMod x5 x3 x4
  let v4 : W := MachineState.readWord s.memory 160
  {s with pc := N 6757, memory := s.memory, stack := v4 :: x14 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem sq8p1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p1P {s with pc := N 6747, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (sq8p1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p1P, sq8p1M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def sq8p2P : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]

def sq8p2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 128
  let v3 : W := MachineState.readWord s.memory 32
  {s with pc := N 6767, memory := s.memory, stack := v3 :: v2 :: x12 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq8p2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p2P {s with pc := N 6757, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq8p2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p2P, sq8p2M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha128, hf128]


def sq8p3P : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD]

def sq8p3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := UInt256.mulMod v3 v2 x13
  {s with pc := N 6777, memory := s.memory, stack := v4 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq8p3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p3P {s with pc := N 6767, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq8p3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p3P, sq8p3M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha96, hf96]


def sq8p4P : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 2 1088,
   .op .MLOAD]

def sq8p4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := v0 + v0
  let v2 : W := x3 + v1
  let v3 : W := x3 + x2
  let v4 : W := MachineState.readWord s.memory 1088
  {s with pc := N 6788, memory := s.memory, stack := v4 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq8p4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p4P {s with pc := N 6777, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq8p4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p4P, sq8p4M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def sq8p5P : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq8p5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x11 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := x9 * v2
  let v4 : W := v3 + v1
  {s with pc := N 6797, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq8p5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p5P {s with pc := N 6788, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq8p5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p5P, sq8p5M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def sq8p6P : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def sq8p6M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := v0 * x3
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 6806, memory := s.memory, stack := v3 :: x7 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq8p6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p6P {s with pc := N 6797, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq8p6M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p6P, sq8p6M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha224, hf224]


def sq8p7P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def sq8p7M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 1216
  let v3 : W := v2 * x6
  let v4 : W := v3 + v1
  {s with pc := N 6816, memory := s.memory, stack := x16 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq8p7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p7P {s with pc := N 6806, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq8p7M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p7P, sq8p7M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def sq8p8P : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def sq8p8M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x6 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 1280
  let v3 : W := v2 * x3
  let v4 : W := v3 + v1
  {s with pc := N 6826, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq8p8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p8P {s with pc := N 6816, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq8p8M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p8P, sq8p8M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def sq8p9P : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1088,
   .op .MLOAD]

def sq8p9M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x13 * x11
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 1088
  {s with pc := N 6836, memory := s.memory, stack := v2 :: x9 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq8p9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p9P {s with pc := N 6826, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq8p9M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p9P, sq8p9M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1088, hf1088]


def sq8p10P : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def sq8p10M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x12 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := UInt256.mulMod x10 v2 x11
  {s with pc := N 6845, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq8p10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p10P {s with pc := N 6836, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq8p10M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p10P, sq8p10M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192]


def sq8p11P : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq8p11M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := UInt256.mulMod v1 x4 x10
  let v3 : W := v2 + v0
  {s with pc := N 6853, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq8p11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p11P {s with pc := N 6845, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq8p11M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p11P, sq8p11M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def sq8p12P : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def sq8p12M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := UInt256.mulMod v0 x8 x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 1216
  {s with pc := N 6865, memory := s.memory, stack := v3 :: x5 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq8p12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq8p12P {s with pc := N 6853, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq8p12M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq8p12P, sq8p12M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


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

def squareColumn8Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := v0 * carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := MachineState.readWord s.memory 64
  let v5 : W := v4 * v3
  let v6 : W := v5 + v2
  let v7 : W := v6 + v6
  let v8 : W := UInt256.mulMod w3 w1 w2
  let v9 : W := MachineState.readWord s.memory 160
  let v10 : W := UInt256.mulMod w9 v9 w12
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord s.memory 128
  let v13 : W := MachineState.readWord s.memory 32
  let v14 : W := UInt256.mulMod v13 v12 w12
  let v15 : W := v14 + v11
  let v16 : W := MachineState.readWord s.memory 96
  let v17 : W := MachineState.readWord s.memory 64
  let v18 : W := UInt256.mulMod v17 v16 w12
  let v19 : W := v18 + v15
  let v20 : W := v19 + v19
  let v21 : W := w4 + v20
  let v22 : W := w4 + v7
  let v23 : W := MachineState.readWord s.memory 1088
  let v24 : W := w13 * v23
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 192
  let v27 : W := w11 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 0
  let v30 : W := v29 * w6
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 224
  let v33 : W := v32 * w10
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 1216
  let v36 : W := v35 * w7
  let v37 : W := v36 + v34
  let v38 : W := w8 * w17
  let v39 : W := v38 + v37
  let v40 : W := MachineState.readWord s.memory 1280
  let v41 : W := v40 * w5
  let v42 : W := v41 + v39
  let v43 : W := w16 * w14
  let v44 : W := v43 + v42
  let v45 : W := MachineState.readWord s.memory 1088
  let v46 : W := UInt256.mulMod w13 v45 w12
  let v47 : W := v46 + v21
  let v48 : W := MachineState.readWord s.memory 192
  let v49 : W := UInt256.mulMod w11 v48 w12
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord s.memory 0
  let v52 : W := UInt256.mulMod v51 w6 w12
  let v53 : W := v52 + v50
  let v54 : W := MachineState.readWord s.memory 224
  let v55 : W := UInt256.mulMod v54 w10 w12
  let v56 : W := v55 + v53
  let v57 : W := MachineState.readWord s.memory 1216
  {s with pc := N 6865, memory := s.memory, stack := v57 :: w7 :: w12 :: v56 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest}

theorem squareColumn8_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8Program {s with pc := N 6736, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} =
      some (squareColumn8Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 rest) := by
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := v0 * carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := MachineState.readWord s.memory 64
  let v5 : W := v4 * v3
  let v6 : W := v5 + v2
  let v7 : W := v6 + v6
  let v8 : W := UInt256.mulMod w3 w1 w2
  let v9 : W := MachineState.readWord s.memory 160
  let v10 : W := UInt256.mulMod w9 v9 w12
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord s.memory 128
  let v13 : W := MachineState.readWord s.memory 32
  let v14 : W := UInt256.mulMod v13 v12 w12
  let v15 : W := v14 + v11
  let v16 : W := MachineState.readWord s.memory 96
  let v17 : W := MachineState.readWord s.memory 64
  let v18 : W := UInt256.mulMod v17 v16 w12
  let v19 : W := v18 + v15
  let v20 : W := v19 + v19
  let v21 : W := w4 + v20
  let v22 : W := w4 + v7
  let v23 : W := MachineState.readWord s.memory 1088
  let v24 : W := w13 * v23
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 192
  let v27 : W := w11 * v26
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 0
  let v30 : W := v29 * w6
  let v31 : W := v30 + v28
  let v32 : W := MachineState.readWord s.memory 224
  let v33 : W := v32 * w10
  let v34 : W := v33 + v31
  let v35 : W := MachineState.readWord s.memory 1216
  let v36 : W := v35 * w7
  let v37 : W := v36 + v34
  let v38 : W := w8 * w17
  let v39 : W := v38 + v37
  let v40 : W := MachineState.readWord s.memory 1280
  let v41 : W := v40 * w5
  let v42 : W := v41 + v39
  let v43 : W := w16 * w14
  let v44 : W := v43 + v42
  let v45 : W := MachineState.readWord s.memory 1088
  let v46 : W := UInt256.mulMod w13 v45 w12
  let v47 : W := v46 + v21
  let v48 : W := MachineState.readWord s.memory 192
  let v49 : W := UInt256.mulMod w11 v48 w12
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord s.memory 0
  let v52 : W := UInt256.mulMod v51 w6 w12
  let v53 : W := v52 + v50
  let v54 : W := MachineState.readWord s.memory 224
  let v55 : W := UInt256.mulMod v54 w10 w12
  let v56 : W := v55 + v53
  let v57 : W := MachineState.readWord s.memory 1216
  have h0 : runInstructions sq8p0P {s with pc := N 6736, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6747, memory := s.memory, stack := v4 :: v3 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p0M, v0, v1, v2, v3, v4] using sq8p0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h1 : runInstructions sq8p1P {s with pc := N 6747, memory := s.memory, stack := v4 :: v3 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6757, memory := s.memory, stack := v9 :: w12 :: v8 :: v7 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p1M, v5, v6, v7, v8, v9] using sq8p1_run (s) (v4) (v3) (v2) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h2 : runInstructions sq8p2P {s with pc := N 6757, memory := s.memory, stack := v9 :: w12 :: v8 :: v7 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6767, memory := s.memory, stack := v13 :: v12 :: w12 :: v11 :: v7 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p2M, v10, v11, v12, v13] using sq8p2_run (s) (v9) (w12) (v8) (v7) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h3 : runInstructions sq8p3P {s with pc := N 6767, memory := s.memory, stack := v13 :: v12 :: w12 :: v11 :: v7 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6777, memory := s.memory, stack := v18 :: v15 :: v7 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p3M, v14, v15, v16, v17, v18] using sq8p3_run (s) (v13) (v12) (w12) (v11) (v7) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h4 : runInstructions sq8p4P {s with pc := N 6777, memory := s.memory, stack := v18 :: v15 :: v7 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6788, memory := s.memory, stack := v23 :: v22 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p4M, v19, v20, v21, v22, v23] using sq8p4_run (s) (v18) (v15) (v7) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h5 : runInstructions sq8p5P {s with pc := N 6788, memory := s.memory, stack := v23 :: v22 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6797, memory := s.memory, stack := v28 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p5M, v24, v25, v26, v27, v28] using sq8p5_run (s) (v23) (v22) (v21) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h6 : runInstructions sq8p6P {s with pc := N 6797, memory := s.memory, stack := v28 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6806, memory := s.memory, stack := v32 :: w10 :: v31 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p6M, v29, v30, v31, v32] using sq8p6_run (s) (v28) (v21) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h7 : runInstructions sq8p7P {s with pc := N 6806, memory := s.memory, stack := v32 :: w10 :: v31 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6816, memory := s.memory, stack := w17 :: v37 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p7M, v33, v34, v35, v36, v37] using sq8p7_run (s) (v32) (w10) (v31) (v21) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h8 : runInstructions sq8p8P {s with pc := N 6816, memory := s.memory, stack := w17 :: v37 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6826, memory := s.memory, stack := v42 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p8M, v38, v39, v40, v41, v42] using sq8p8_run (s) (w17) (v37) (v21) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h9 : runInstructions sq8p9P {s with pc := N 6826, memory := s.memory, stack := v42 :: v21 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6836, memory := s.memory, stack := v45 :: w12 :: v21 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p9M, v43, v44, v45] using sq8p9_run (s) (v42) (v21) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h10 : runInstructions sq8p10P {s with pc := N 6836, memory := s.memory, stack := v45 :: w12 :: v21 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6845, memory := s.memory, stack := v49 :: v47 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p10M, v46, v47, v48, v49] using sq8p10_run (s) (v45) (w12) (v21) (v44) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h11 : runInstructions sq8p11P {s with pc := N 6845, memory := s.memory, stack := v49 :: v47 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6853, memory := s.memory, stack := w12 :: v53 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p11M, v50, v51, v52, v53] using sq8p11_run (s) (v49) (v47) (v44) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  have h12 : runInstructions sq8p12P {s with pc := N 6853, memory := s.memory, stack := w12 :: v53 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} = some {s with pc := N 6865, memory := s.memory, stack := v57 :: w7 :: w12 :: v56 :: v44 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: rest} := by
    simpa only [sq8p12M, v54, v55, v56, v57] using sq8p12_run (s) (w12) (v53) (v44) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) (w18) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
