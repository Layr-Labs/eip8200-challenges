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

def sq6p0P : List Instr :=
  [.push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD]

def sq6p0M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1248
  let v1 : W := UInt256.mulMod v0 x0 x1
  let v2 : W := v1 + x2
  let v3 : W := MachineState.readWord s.memory 2720
  {s with pc := N 6579, memory := s.memory, stack := v3 :: x15 :: x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq6p0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p0P {s with pc := N 6567, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq6p0M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : W).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p0P, sq6p0M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248, ha2720, hf2720]


def sq6p1P : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1280,
   .op .MSTORE]

def sq6p1M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := UInt256.land x15 v0
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 1280
  {s with pc := N 6589, memory := v2, stack := v1 :: x1 :: x2 :: x3 :: x2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq6p1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p1P {s with pc := N 6579, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq6p1M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p1P, sq6p1M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def sq6p2P : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 768,
   .op .MLOAD]

def sq6p2M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod (N 2048) v1 x4
  let v3 : W := MachineState.readWord s.memory 768
  {s with pc := N 6601, memory := s.memory, stack := v3 :: x12 :: x18 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq6p2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p2P {s with pc := N 6589, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq6p2M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p2P, sq6p2M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]


def sq6p3P : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def sq6p3M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x2 * x0
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := v1 * x7
  let v3 : W := v2 + v0
  {s with pc := N 6610, memory := s.memory, stack := v3 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq6p3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p3P {s with pc := N 6601, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq6p3M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p3P, sq6p3M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def sq6p4P : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]

def sq6p4M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := x9 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := MachineState.readWord s.memory 32
  {s with pc := N 6622, memory := s.memory, stack := v4 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq6p4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p4P {s with pc := N 6610, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq6p4M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p4P, sq6p4M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha96, hf96, ha128, hf128]


def sq6p5P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def sq6p5M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := v1 + v1
  let v3 : W := UInt256.mulMod x5 x3 x4
  let v4 : W := MachineState.readWord s.memory 160
  {s with pc := N 6632, memory := s.memory, stack := v4 :: x14 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem sq6p5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p5P {s with pc := N 6622, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (sq6p5M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p5P, sq6p5M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def sq6p6P : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD]

def sq6p6M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 128
  let v3 : W := UInt256.mulMod x9 v2 x12
  {s with pc := N 6641, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq6p6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p6P {s with pc := N 6632, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq6p6M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p6P, sq6p6M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def sq6p7P : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def sq6p7M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 96
  let v2 : W := MachineState.readWord s.memory 32
  let v3 : W := UInt256.mulMod v2 v1 x11
  let v4 : W := v3 + v0
  {s with pc := N 6651, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq6p7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p7P {s with pc := N 6641, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq6p7M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p7P, sq6p7M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha96, hf96]


def sq6p8P : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 64,
   .op .MLOAD]

def sq6p8M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x0
  let v1 : W := x2 + v0
  let v2 : W := x2 + x1
  let v3 : W := MachineState.readWord s.memory 64
  {s with pc := N 6660, memory := s.memory, stack := v3 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq6p8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p8P {s with pc := N 6651, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq6p8M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p8P, sq6p8M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]


def sq6p9P : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 1600,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Swap ⟨2, by decide⟩)]

def sq6p9M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 1600
  {s with pc := N 6670, memory := s.memory, stack := x2 :: x11 :: v1 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v2 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq6p9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p9P {s with pc := N 6660, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq6p9M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1600 : (1600 : W).toNat = 1600 := rfl
  have hf1600 := Monpro.activeWords_fix s 1600 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p9P, sq6p9M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1600, hf1600]


def sq6p10P : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq6p10M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x1 x11
  let v1 : W := v0 + x0
  let v2 : W := x3 * x1
  let v3 : W := v2 + x2
  {s with pc := N 6678, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq6p10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p10P {s with pc := N 6670, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq6p10M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq6p10P, sq6p10M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def sq6p11P : List Instr :=
  [.push 2 1088,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def sq6p11M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1088
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 192
  {s with pc := N 6689, memory := s.memory, stack := v3 :: x3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq6p11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p11P {s with pc := N 6678, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq6p11M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  have ha1088 : (1088 : W).toNat = 1088 := rfl
  have hf1088 := Monpro.activeWords_fix s 1088 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p11P, sq6p11M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha192, hf192, ha1088, hf1088]


def sq6p12P : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]

def sq6p12M (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := v2 * x9
  {s with pc := N 6695, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq6p12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq6p12P {s with pc := N 6689, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq6p12M s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq6p12P, sq6p12M, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


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

def squareColumn6Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1248
  let v1 : W := UInt256.mulMod v0 carry w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord s.memory 2720
  let v4 : W := w2 * v3
  let v5 : W := UInt256.land w13 v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 1280
  let v7 : W := UInt256.mulMod v5 w14 w10
  let v8 : W := v7 + v2
  let v9 : W := UInt256.mulMod (N 2048) v8 w10
  let v10 : W := MachineState.readWord v6 768
  let v11 : W := w16 * v10
  let v12 : W := MachineState.readWord v6 160
  let v13 : W := v12 * w6
  let v14 : W := v13 + v11
  let v15 : W := MachineState.readWord v6 128
  let v16 : W := w7 * v15
  let v17 : W := v16 + v14
  let v18 : W := MachineState.readWord v6 96
  let v19 : W := MachineState.readWord v6 32
  let v20 : W := v19 * v18
  let v21 : W := v20 + v17
  let v22 : W := v21 + v21
  let v23 : W := UInt256.mulMod w16 v10 w10
  let v24 : W := MachineState.readWord v6 160
  let v25 : W := UInt256.mulMod w6 v24 w10
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord v6 128
  let v28 : W := UInt256.mulMod w7 v27 w10
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord v6 96
  let v31 : W := MachineState.readWord v6 32
  let v32 : W := UInt256.mulMod v31 v30 w10
  let v33 : W := v32 + v29
  let v34 : W := v33 + v33
  let v35 : W := v9 + v34
  let v36 : W := v9 + v22
  let v37 : W := MachineState.readWord v6 64
  let v38 : W := v37 * v37
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord v6 1600
  let v41 : W := UInt256.mulMod v40 w11 w10
  let v42 : W := v41 + v35
  let v43 : W := v40 * w11
  let v44 : W := v43 + v39
  let v45 : W := MachineState.readWord v6 1088
  let v46 : W := w9 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord v6 192
  let v49 : W := v48 * w4
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord v6 0
  let v52 : W := v51 * w8
  {s with pc := N 6695, memory := v6, stack := v52 :: v50 :: v42 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest}

theorem squareColumn6_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn6Program {s with pc := N 6567, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} =
      some (squareColumn6Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 rest) := by
  let v0 : W := MachineState.readWord s.memory 1248
  let v1 : W := UInt256.mulMod v0 carry w0
  let v2 : W := v1 + w1
  let v3 : W := MachineState.readWord s.memory 2720
  let v4 : W := w2 * v3
  let v5 : W := UInt256.land w13 v4
  let v6 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v5.toNat 32) 1280
  let v7 : W := UInt256.mulMod v5 w14 w10
  let v8 : W := v7 + v2
  let v9 : W := UInt256.mulMod (N 2048) v8 w10
  let v10 : W := MachineState.readWord v6 768
  let v11 : W := w16 * v10
  let v12 : W := MachineState.readWord v6 160
  let v13 : W := v12 * w6
  let v14 : W := v13 + v11
  let v15 : W := MachineState.readWord v6 128
  let v16 : W := w7 * v15
  let v17 : W := v16 + v14
  let v18 : W := MachineState.readWord v6 96
  let v19 : W := MachineState.readWord v6 32
  let v20 : W := v19 * v18
  let v21 : W := v20 + v17
  let v22 : W := v21 + v21
  let v23 : W := UInt256.mulMod w16 v10 w10
  let v24 : W := MachineState.readWord v6 160
  let v25 : W := UInt256.mulMod w6 v24 w10
  let v26 : W := v25 + v23
  let v27 : W := MachineState.readWord v6 128
  let v28 : W := UInt256.mulMod w7 v27 w10
  let v29 : W := v28 + v26
  let v30 : W := MachineState.readWord v6 96
  let v31 : W := MachineState.readWord v6 32
  let v32 : W := UInt256.mulMod v31 v30 w10
  let v33 : W := v32 + v29
  let v34 : W := v33 + v33
  let v35 : W := v9 + v34
  let v36 : W := v9 + v22
  let v37 : W := MachineState.readWord v6 64
  let v38 : W := v37 * v37
  let v39 : W := v38 + v36
  let v40 : W := MachineState.readWord v6 1600
  let v41 : W := UInt256.mulMod v40 w11 w10
  let v42 : W := v41 + v35
  let v43 : W := v40 * w11
  let v44 : W := v43 + v39
  let v45 : W := MachineState.readWord v6 1088
  let v46 : W := w9 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord v6 192
  let v49 : W := v48 * w4
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord v6 0
  let v52 : W := v51 * w8
  have h0 : runInstructions sq6p0P {s with pc := N 6567, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6579, memory := s.memory, stack := v3 :: w14 :: w10 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p0M, v0, v1, v2, v3] using sq6p0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h1 : runInstructions sq6p1P {s with pc := N 6579, memory := s.memory, stack := v3 :: w14 :: w10 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6589, memory := v6, stack := v5 :: w14 :: w10 :: v2 :: w10 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p1M, v4, v5, v6] using sq6p1_run (s) (v3) (w14) (w10) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h2 : runInstructions sq6p2P {s with pc := N 6589, memory := v6, stack := v5 :: w14 :: w10 :: v2 :: w10 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6601, memory := v6, stack := v10 :: w10 :: w16 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p2M, v7, v8, v9, v10] using sq6p2_run ({s with memory := v6}) (v5) (w14) (w10) (v2) (w10) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h3 : runInstructions sq6p3P {s with pc := N 6601, memory := v6, stack := v10 :: w10 :: w16 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6610, memory := v6, stack := v14 :: v10 :: w10 :: w16 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p3M, v11, v12, v13, v14] using sq6p3_run ({s with memory := v6}) (v10) (w10) (w16) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h4 : runInstructions sq6p4P {s with pc := N 6610, memory := v6, stack := v14 :: v10 :: w10 :: w16 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6622, memory := v6, stack := v19 :: v18 :: v17 :: v10 :: w10 :: w16 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p4M, v15, v16, v17, v18, v19] using sq6p4_run ({s with memory := v6}) (v14) (v10) (w10) (w16) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h5 : runInstructions sq6p5P {s with pc := N 6622, memory := v6, stack := v19 :: v18 :: v17 :: v10 :: w10 :: w16 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6632, memory := v6, stack := v24 :: w10 :: v23 :: v22 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p5M, v20, v21, v22, v23, v24] using sq6p5_run ({s with memory := v6}) (v19) (v18) (v17) (v10) (w10) (w16) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h6 : runInstructions sq6p6P {s with pc := N 6632, memory := v6, stack := v24 :: w10 :: v23 :: v22 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6641, memory := v6, stack := v28 :: v26 :: v22 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p6M, v25, v26, v27, v28] using sq6p6_run ({s with memory := v6}) (v24) (w10) (v23) (v22) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h7 : runInstructions sq6p7P {s with pc := N 6641, memory := v6, stack := v28 :: v26 :: v22 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6651, memory := v6, stack := v33 :: v22 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p7M, v29, v30, v31, v32, v33] using sq6p7_run ({s with memory := v6}) (v28) (v26) (v22) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h8 : runInstructions sq6p8P {s with pc := N 6651, memory := v6, stack := v33 :: v22 :: v9 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6660, memory := v6, stack := v37 :: v36 :: v35 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p8M, v34, v35, v36, v37] using sq6p8_run ({s with memory := v6}) (v33) (v22) (v9) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h9 : runInstructions sq6p9P {s with pc := N 6660, memory := v6, stack := v37 :: v36 :: v35 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6670, memory := v6, stack := v35 :: w11 :: v39 :: v40 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p9M, v38, v39, v40] using sq6p9_run ({s with memory := v6}) (v37) (v36) (v35) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h10 : runInstructions sq6p10P {s with pc := N 6670, memory := v6, stack := v35 :: w11 :: v39 :: v40 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6678, memory := v6, stack := v44 :: v42 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p10M, v41, v42, v43, v44] using sq6p10_run ({s with memory := v6}) (v35) (w11) (v39) (v40) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (v40) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h11 : runInstructions sq6p11P {s with pc := N 6678, memory := v6, stack := v44 :: v42 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6689, memory := v6, stack := v48 :: w4 :: v47 :: v42 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p11M, v45, v46, v47, v48] using sq6p11_run ({s with memory := v6}) (v44) (v42) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (v40) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  have h12 : runInstructions sq6p12P {s with pc := N 6689, memory := v6, stack := v48 :: w4 :: v47 :: v42 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} = some {s with pc := N 6695, memory := v6, stack := v52 :: v50 :: v42 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: v40 :: w12 :: w13 :: w14 :: w15 :: w16 :: rest} := by
    simpa only [sq6p12M, v49, v50, v51, v52] using sq6p12_run ({s with memory := v6}) (v48) (w4) (v47) (v42) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (v40) (w12) (w13) (w14) (w15) (w16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
