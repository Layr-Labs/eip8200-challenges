import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs

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

def pr6p0P : List Instr :=
  [.push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .push 0 0,
   .op .MLOAD]

def pr6p0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := UInt256.mulMod v0 x0 x1
  let v2 : W := v1 + x2
  let v3 : W := MachineState.readWord s.memory 0
  {s with pc := N 8383, memory := s.memory, stack := v3 :: x16 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr6p0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p0P {s with pc := N 8374, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr6p0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p0P, pr6p0M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha192, hf192]


def pr6p1P : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def pr6p1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := UInt256.mulMod v2 x5 x12
  let v4 : W := v3 + v1
  {s with pc := N 8392, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem pr6p1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p1P {s with pc := N 8383, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (pr6p1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p1P, pr6p1M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def pr6p2P : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA12),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14)]

def pr6p2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := UInt256.mulMod v0 x11 x9
  let v2 : W := v1 + x0
  {s with pc := N 8402, memory := s.memory, stack := x13 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr6p2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p2P {s with pc := N 8392, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr6p2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p2P, pr6p2M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def pr6p3P : List Instr :=
  [.push 2 2720,
   .op .MLOAD,
   .op (.Dup dA2),
   .op (.Swap sA4),
   .op .MUL,
   .op (.Dup dA15),
   .op .AND,
   .op (.Dup dA0)]

def pr6p3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := x3 * v0
  let v2 : W := UInt256.land x14 v1
  {s with pc := N 8412, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr6p3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p3P {s with pc := N 8402, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr6p3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p3P, pr6p3M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def pr6p4P : List Instr :=
  [.push 2 1248,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1568,
   .op .MLOAD]

def pr6p4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1248
  let v1 : W := UInt256.mulMod x1 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := UInt256.mulMod (N 2048) v2 x5
  let v4 : W := MachineState.readWord v0 1568
  {s with pc := N 8426, memory := v0, stack := v4 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr6p4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p4P {s with pc := N 8412, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr6p4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha1568 : (1568 : W).toNat = 1568 := rfl
  have hf1568 := Monpro.activeWords_fix s 1568 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p4P, pr6p4M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248, ha1568, hf1568]


def pr6p5P : List Instr :=
  [.op (.Swap sA7),
   .op (.Dup dA1),
   .op (.Dup dA10),
   .push 2 768,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA4)]

def pr6p5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 2016
  {s with pc := N 8438, memory := s.memory, stack := x1 :: v0 :: x9 :: x1 :: x8 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x0 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem pr6p5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p5P {s with pc := N 8426, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (pr6p5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p5P, pr6p5M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768, ha2016, hf2016]


def pr6p6P : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10)]

def pr6p6M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x5 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x5 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 8446, memory := s.memory, stack := x13 :: v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr6p6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p6P {s with pc := N 8438, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr6p6M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr6p6P, pr6p6M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def pr6p7P : List Instr :=
  [.op (.Dup dA7),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA4),
   .op (.Dup dA1),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD]

def pr6p7M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1984
  let v1 : W := v0 * x7
  let v2 : W := v1 + x3
  {s with pc := N 8456, memory := s.memory, stack := v2 :: x7 :: x0 :: x1 :: x2 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr6p7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p7P {s with pc := N 8446, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr6p7M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p7P, pr6p7M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1984, hf1984]


def pr6p8P : List Instr :=
  [.op (.Swap sA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA8),
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap sA4)]

def pr6p8M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 1952
  {s with pc := N 8466, memory := s.memory, stack := x0 :: x10 :: x13 :: v1 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr6p8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p8P {s with pc := N 8456, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr6p8M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p8P, pr6p8M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1952, hf1952]


def pr6p9P : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10)]

def pr6p9M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x5 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x5 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 8474, memory := s.memory, stack := x13 :: v3 :: x4 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr6p9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p9P {s with pc := N 8466, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr6p9M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr6p9P, pr6p9M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def pr6p10P : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap sA4),
   .op (.Dup dA1),
   .op (.Dup dA6),
   .op .MUL]

def pr6p10M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := MachineState.readWord s.memory 1920
  let v2 : W := v1 * v0
  {s with pc := N 8485, memory := s.memory, stack := v2 :: x3 :: v0 :: x0 :: x1 :: x2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem pr6p10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p10P {s with pc := N 8474, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (pr6p10M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p10P, pr6p10M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha1920, hf1920]


def pr6p11P : List Instr :=
  [.op .ADD,
   .op (.Swap sA4),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA10),
   .push 1 64,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD]

def pr6p11M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x6 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := MachineState.readWord s.memory 1888
  {s with pc := N 8497, memory := s.memory, stack := v4 :: v3 :: x14 :: v2 :: x5 :: v0 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem pr6p11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p11P {s with pc := N 8485, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (pr6p11M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, pr6p11P, pr6p11M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha1888, hf1888]


def pr6p12P : List Instr :=
  [.op (.Swap sA4),
   .op (.Dup dA1),
   .op (.Dup dA6),
   .op .MUL,
   .op .ADD]

def pr6p12M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x5
  {s with pc := N 8502, memory := s.memory, stack := v1 :: x1 :: x2 :: x3 :: x4 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem pr6p12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions pr6p12P {s with pc := N 8497, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (pr6p12M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, pr6p12P, pr6p12M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn6Program : List Instr :=
  [
  .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 2 1216,
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
   .push 2 1248,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1568,
   .op .MLOAD,
   .op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .push 2 768,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn6Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := UInt256.mulMod v0 carry w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := UInt256.mulMod v3 w15 w10
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 224
  let v7 : W := UInt256.mulMod v6 w3 w10
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 1216
  let v10 : W := UInt256.mulMod v9 w12 w10
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord s.memory 2720
  let v13 : W := w2 * v12
  let v14 : W := UInt256.land w13 v13
  let v15 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v14.toNat 32) 1248
  let v16 : W := UInt256.mulMod v14 w14 w10
  let v17 : W := v16 + v11
  let v18 : W := UInt256.mulMod (N 2048) v17 w10
  let v19 : W := MachineState.readWord v15 1568
  let v20 : W := MachineState.readWord v15 768
  let v21 : W := MachineState.readWord v15 2016
  let v22 : W := v21 * v20
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod v21 v20 w10
  let v25 : W := v24 + v18
  let v26 : W := MachineState.readWord v15 1984
  let v27 : W := v26 * w6
  let v28 : W := v27 + v23
  let v29 : W := UInt256.mulMod v26 w6 w10
  let v30 : W := v29 + v25
  let v31 : W := MachineState.readWord v15 1952
  let v32 : W := v31 * w7
  let v33 : W := v32 + v28
  let v34 : W := UInt256.mulMod v31 w7 w10
  let v35 : W := v34 + v30
  let v36 : W := MachineState.readWord v15 32
  let v37 : W := MachineState.readWord v15 1920
  let v38 : W := v37 * v36
  let v39 : W := v38 + v33
  let v40 : W := UInt256.mulMod v37 v36 w10
  let v41 : W := v40 + v35
  let v42 : W := MachineState.readWord v15 64
  let v43 : W := MachineState.readWord v15 1888
  let v44 : W := v43 * v42
  let v45 : W := v44 + v39
  {s with pc := N 8502, memory := v15, stack := v45 :: v42 :: w10 :: v41 :: w9 :: v43 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem productColumn6_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6Program {s with pc := N 8374, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} =
      some (productColumn6Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := UInt256.mulMod v0 carry w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := UInt256.mulMod v3 w15 w10
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 224
  let v7 : W := UInt256.mulMod v6 w3 w10
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 1216
  let v10 : W := UInt256.mulMod v9 w12 w10
  let v11 : W := v10 + v8
  let v12 : W := MachineState.readWord s.memory 2720
  let v13 : W := w2 * v12
  let v14 : W := UInt256.land w13 v13
  let v15 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v14.toNat 32) 1248
  let v16 : W := UInt256.mulMod v14 w14 w10
  let v17 : W := v16 + v11
  let v18 : W := UInt256.mulMod (N 2048) v17 w10
  let v19 : W := MachineState.readWord v15 1568
  let v20 : W := MachineState.readWord v15 768
  let v21 : W := MachineState.readWord v15 2016
  let v22 : W := v21 * v20
  let v23 : W := v22 + v18
  let v24 : W := UInt256.mulMod v21 v20 w10
  let v25 : W := v24 + v18
  let v26 : W := MachineState.readWord v15 1984
  let v27 : W := v26 * w6
  let v28 : W := v27 + v23
  let v29 : W := UInt256.mulMod v26 w6 w10
  let v30 : W := v29 + v25
  let v31 : W := MachineState.readWord v15 1952
  let v32 : W := v31 * w7
  let v33 : W := v32 + v28
  let v34 : W := UInt256.mulMod v31 w7 w10
  let v35 : W := v34 + v30
  let v36 : W := MachineState.readWord v15 32
  let v37 : W := MachineState.readWord v15 1920
  let v38 : W := v37 * v36
  let v39 : W := v38 + v33
  let v40 : W := UInt256.mulMod v37 v36 w10
  let v41 : W := v40 + v35
  let v42 : W := MachineState.readWord v15 64
  let v43 : W := MachineState.readWord v15 1888
  let v44 : W := v43 * v42
  let v45 : W := v44 + v39
  have h0 : runInstructions pr6p0P {s with pc := N 8374, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8383, memory := s.memory, stack := v3 :: w15 :: w10 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p0M, v0, v1, v2, v3] using pr6p0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions pr6p1P {s with pc := N 8383, memory := s.memory, stack := v3 :: w15 :: w10 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8392, memory := s.memory, stack := v8 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p1M, v4, v5, v6, v7, v8] using pr6p1_run (s) (v3) (w15) (w10) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions pr6p2P {s with pc := N 8392, memory := s.memory, stack := v8 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8402, memory := s.memory, stack := w14 :: w10 :: v11 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p2M, v9, v10, v11] using pr6p2_run (s) (v8) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions pr6p3P {s with pc := N 8402, memory := s.memory, stack := w14 :: w10 :: v11 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8412, memory := s.memory, stack := v14 :: v14 :: w14 :: w10 :: v11 :: w10 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p3M, v12, v13, v14] using pr6p3_run (s) (w14) (w10) (v11) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions pr6p4P {s with pc := N 8412, memory := s.memory, stack := v14 :: v14 :: w14 :: w10 :: v11 :: w10 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8426, memory := v15, stack := v19 :: v18 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p4M, v15, v16, v17, v18, v19] using pr6p4_run (s) (v14) (v14) (w14) (w10) (v11) (w10) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h5 : runInstructions pr6p5P {s with pc := N 8426, memory := v15, stack := v19 :: v18 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8438, memory := v15, stack := v18 :: v20 :: w10 :: v18 :: w9 :: v21 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p5M, v20, v21] using pr6p5_run ({s with memory := v15}) (v19) (v18) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h6 : runInstructions pr6p6P {s with pc := N 8438, memory := v15, stack := v18 :: v20 :: w10 :: v18 :: w9 :: v21 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8446, memory := v15, stack := w10 :: v25 :: w9 :: v23 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p6M, v22, v23, v24, v25] using pr6p6_run ({s with memory := v15}) (v18) (v20) (w10) (v18) (w9) (v21) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h7 : runInstructions pr6p7P {s with pc := N 8446, memory := v15, stack := w10 :: v25 :: w9 :: v23 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8456, memory := v15, stack := v28 :: w6 :: w10 :: v25 :: w9 :: v26 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p7M, v26, v27, v28] using pr6p7_run ({s with memory := v15}) (w10) (v25) (w9) (v23) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h8 : runInstructions pr6p8P {s with pc := N 8456, memory := v15, stack := v28 :: w6 :: w10 :: v25 :: w9 :: v26 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8466, memory := v15, stack := v28 :: w7 :: w10 :: v30 :: w9 :: v31 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p8M, v29, v30, v31] using pr6p8_run ({s with memory := v15}) (v28) (w6) (w10) (v25) (w9) (v26) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h9 : runInstructions pr6p9P {s with pc := N 8466, memory := v15, stack := v28 :: w7 :: w10 :: v30 :: w9 :: v31 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8474, memory := v15, stack := w10 :: v35 :: w9 :: v33 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p9M, v32, v33, v34, v35] using pr6p9_run ({s with memory := v15}) (v28) (w7) (w10) (v30) (w9) (v31) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h10 : runInstructions pr6p10P {s with pc := N 8474, memory := v15, stack := w10 :: v35 :: w9 :: v33 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8485, memory := v15, stack := v38 :: v33 :: v36 :: w10 :: v35 :: w9 :: v37 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p10M, v36, v37, v38] using pr6p10_run ({s with memory := v15}) (w10) (v35) (w9) (v33) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h11 : runInstructions pr6p11P {s with pc := N 8485, memory := v15, stack := v38 :: v33 :: v36 :: w10 :: v35 :: w9 :: v37 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8497, memory := v15, stack := v43 :: v42 :: w10 :: v41 :: w9 :: v39 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p11M, v39, v40, v41, v42, v43] using pr6p11_run ({s with memory := v15}) (v38) (v33) (v36) (w10) (v35) (w9) (v37) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h12 : runInstructions pr6p12P {s with pc := N 8497, memory := v15, stack := v43 :: v42 :: w10 :: v41 :: w9 :: v39 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 8502, memory := v15, stack := v45 :: v42 :: w10 :: v41 :: w9 :: v43 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [pr6p12M, v44, v45] using pr6p12_run ({s with memory := v15}) (v43) (v42) (w10) (v41) (w9) (v39) (w3) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
