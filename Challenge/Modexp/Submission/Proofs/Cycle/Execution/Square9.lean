import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
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

open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

open CycleSubmission.Prepared.Arithmetic

def sq9Newpart0Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq9Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x8 x17 x12
  let v3 : W := v2 + v1
  {s with pc := N 6856, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq9Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart0Program {s with pc := N 6848, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq9Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq9Newpart0Program, sq9Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq9Newpart1Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def sq9Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1280
  let v1 : W := UInt256.mulMod v0 x3 x0
  let v2 : W := v1 + x1
  {s with pc := N 6866, memory := s.memory, stack := x14 :: x12 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq9Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart1Program {s with pc := N 6856, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq9Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart1Program, sq9Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1280, hf1280]


def sq9Newpart2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 768,
   .op .MSTORE]

def sq9Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 768
  {s with pc := N 6876, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq9Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart2Program {s with pc := N 6866, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq9Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart2Program, sq9Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768]


def sq9Newpart3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩)]

def sq9Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x9
  {s with pc := N 6892, memory := s.memory, stack := x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq9Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart3Program {s with pc := N 6876, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq9Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq9Newpart3Program, sq9Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq9Newpart4Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .op (.Swap ⟨7, by decide⟩)]

def sq9Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1216
  let v1 : W := MachineState.readWord s.memory 1280
  {s with pc := N 6904, memory := s.memory, stack := x6 :: x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: v0 :: x7 :: x8 :: x9 :: x10 :: v1 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq9Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart4Program {s with pc := N 6892, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq9Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1280 : (1280 : W).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart4Program, sq9Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216, ha1280, hf1280]


def sq9Newpart5Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL]

def sq9Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x2 * x0
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := MachineState.readWord s.memory 32
  let v3 : W := v2 * v1
  {s with pc := N 6914, memory := s.memory, stack := v3 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq9Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart5Program {s with pc := N 6904, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq9Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart5Program, sq9Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha160, hf160]


def sq9Newpart6Program : List Instr :=
  [.op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩)]

def sq9Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 128
  let v2 : W := MachineState.readWord s.memory 64
  let v3 : W := v2 * v1
  let v4 : W := v3 + v0
  {s with pc := N 6924, memory := s.memory, stack := v4 :: v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq9Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart6Program {s with pc := N 6914, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq9Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart6Program, sq9Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha128, hf128]


def sq9Newpart7Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD]

def sq9Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x4 x2 x3
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := MachineState.readWord s.memory 32
  {s with pc := N 6934, memory := s.memory, stack := v3 :: v2 :: x13 :: v1 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq9Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart7Program {s with pc := N 6924, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq9Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart7Program, sq9Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha160, hf160]


def sq9Newpart8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD]

def sq9Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 128
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := UInt256.mulMod v3 v2 x13
  {s with pc := N 6944, memory := s.memory, stack := v4 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem sq9Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart8Program {s with pc := N 6934, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (sq9Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart8Program, sq9Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha128, hf128]


def sq9Newpart9Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .MLOAD]

def sq9Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := v0 + v0
  let v2 : W := x3 + v1
  let v3 : W := x3 + x2
  let v4 : W := MachineState.readWord s.memory 96
  {s with pc := N 6954, memory := s.memory, stack := v4 :: v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq9Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart9Program {s with pc := N 6944, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq9Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart9Program, sq9Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def sq9Newpart10Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq9Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := x11 * v2
  let v4 : W := v3 + v1
  {s with pc := N 6963, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq9Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart10Program {s with pc := N 6954, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq9Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart10Program, sq9Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def sq9Newpart11Program : List Instr :=
  [.push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def sq9Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 6972, memory := s.memory, stack := v3 :: x3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq9Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart11Program {s with pc := N 6963, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq9Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq9Newpart11Program, sq9Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def sq9Newpart12Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def sq9Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  {s with pc := N 6976, memory := s.memory, stack := x8 :: x9 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq9Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9Newpart12Program {s with pc := N 6972, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq9Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq9Newpart12Program, sq9Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq9NewProgram : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 768,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
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
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
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
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def sq9NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w7 w16 w11
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 1280
  let v5 : W := UInt256.mulMod v4 w4 w11
  let v6 : W := v5 + v3
  let v7 : W := UInt256.mulMod w15 w13 w11
  let v8 : W := v7 + v6
  let v9 : W := UInt256.land w14 w3
  let v10 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v9.toNat 32) 768
  let v11 : W := v8 - v9
  let v12 : W := w11 + v11
  let v13 : W := UInt256.mulMod (N 2048) v12 w11
  let v14 : W := MachineState.readWord v10 1216
  let v15 : W := MachineState.readWord v10 1280
  let v16 : W := w17 * w8
  let v17 : W := MachineState.readWord v10 160
  let v18 : W := MachineState.readWord v10 32
  let v19 : W := v18 * v17
  let v20 : W := v19 + v16
  let v21 : W := MachineState.readWord v10 128
  let v22 : W := MachineState.readWord v10 64
  let v23 : W := v22 * v21
  let v24 : W := v23 + v20
  let v25 : W := v24 + v24
  let v26 : W := UInt256.mulMod w17 w8 w11
  let v27 : W := MachineState.readWord v10 160
  let v28 : W := MachineState.readWord v10 32
  let v29 : W := UInt256.mulMod v28 v27 w11
  let v30 : W := v29 + v26
  let v31 : W := MachineState.readWord v10 128
  let v32 : W := MachineState.readWord v10 64
  let v33 : W := UInt256.mulMod v32 v31 w11
  let v34 : W := v33 + v30
  let v35 : W := v34 + v34
  let v36 : W := v13 + v35
  let v37 : W := v13 + v25
  let v38 : W := MachineState.readWord v10 96
  let v39 : W := v38 * v38
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord v10 192
  let v42 : W := w12 * v41
  let v43 : W := v42 + v40
  let v44 : W := MachineState.readWord v10 0
  let v45 : W := w10 * v44
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord v10 224
  let v48 : W := v47 * w5
  let v49 : W := v48 + v46
  {s with pc := N 6976, memory := v10, stack := v14 :: w9 :: v49 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest}

theorem sq9New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq9NewProgram {s with pc := N 6848, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} =
      some (sq9NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w7 w16 w11
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 1280
  let v5 : W := UInt256.mulMod v4 w4 w11
  let v6 : W := v5 + v3
  let v7 : W := UInt256.mulMod w15 w13 w11
  let v8 : W := v7 + v6
  let v9 : W := UInt256.land w14 w3
  let v10 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v9.toNat 32) 768
  let v11 : W := v8 - v9
  let v12 : W := w11 + v11
  let v13 : W := UInt256.mulMod (N 2048) v12 w11
  let v14 : W := MachineState.readWord v10 1216
  let v15 : W := MachineState.readWord v10 1280
  let v16 : W := w17 * w8
  let v17 : W := MachineState.readWord v10 160
  let v18 : W := MachineState.readWord v10 32
  let v19 : W := v18 * v17
  let v20 : W := v19 + v16
  let v21 : W := MachineState.readWord v10 128
  let v22 : W := MachineState.readWord v10 64
  let v23 : W := v22 * v21
  let v24 : W := v23 + v20
  let v25 : W := v24 + v24
  let v26 : W := UInt256.mulMod w17 w8 w11
  let v27 : W := MachineState.readWord v10 160
  let v28 : W := MachineState.readWord v10 32
  let v29 : W := UInt256.mulMod v28 v27 w11
  let v30 : W := v29 + v26
  let v31 : W := MachineState.readWord v10 128
  let v32 : W := MachineState.readWord v10 64
  let v33 : W := UInt256.mulMod v32 v31 w11
  let v34 : W := v33 + v30
  let v35 : W := v34 + v34
  let v36 : W := v13 + v35
  let v37 : W := v13 + v25
  let v38 : W := MachineState.readWord v10 96
  let v39 : W := v38 * v38
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord v10 192
  let v42 : W := w12 * v41
  let v43 : W := v42 + v40
  let v44 : W := MachineState.readWord v10 0
  let v45 : W := w10 * v44
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord v10 224
  let v48 : W := v47 * w5
  let v49 : W := v48 + v46
  have h0 : runInstructions sq9Newpart0Program {s with pc := N 6848, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6856, memory := s.memory, stack := w11 :: v3 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart0Model, v0, v1, v2, v3] using sq9Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h1 : runInstructions sq9Newpart1Program {s with pc := N 6856, memory := s.memory, stack := w11 :: v3 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6866, memory := s.memory, stack := w15 :: w13 :: w11 :: v6 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart1Model, v4, v5, v6] using sq9Newpart1_run (s) (w11) (v3) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h2 : runInstructions sq9Newpart2Program {s with pc := N 6866, memory := s.memory, stack := w15 :: w13 :: w11 :: v6 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6876, memory := v10, stack := v9 :: v8 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart2Model, v7, v8, v9, v10] using sq9Newpart2_run (s) (w15) (w13) (w11) (v6) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h3 : runInstructions sq9Newpart3Program {s with pc := N 6876, memory := v10, stack := v9 :: v8 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6892, memory := v10, stack := w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart3Model, v11, v12, v13] using sq9Newpart3_run ({s with memory := v10}) (v9) (v8) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h4 : runInstructions sq9Newpart4Program {s with pc := N 6892, memory := v10, stack := w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6904, memory := v10, stack := w8 :: w11 :: w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart4Model, v14, v15] using sq9Newpart4_run ({s with memory := v10}) (w17) (v13) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) (w16) (w17) rest hcap hact
  have h5 : runInstructions sq9Newpart5Program {s with pc := N 6904, memory := v10, stack := w8 :: w11 :: w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6914, memory := v10, stack := v19 :: v16 :: w8 :: w11 :: w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart5Model, v16, v17, v18, v19] using sq9Newpart5_run ({s with memory := v10}) (w8) (w11) (w17) (v13) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h6 : runInstructions sq9Newpart6Program {s with pc := N 6914, memory := v10, stack := v19 :: v16 :: w8 :: w11 :: w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6924, memory := v10, stack := v24 :: v24 :: w8 :: w11 :: w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart6Model, v20, v21, v22, v23, v24] using sq9Newpart6_run ({s with memory := v10}) (v19) (v16) (w8) (w11) (w17) (v13) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h7 : runInstructions sq9Newpart7Program {s with pc := N 6924, memory := v10, stack := v24 :: v24 :: w8 :: w11 :: w17 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6934, memory := v10, stack := v28 :: v27 :: w11 :: v26 :: v25 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart7Model, v25, v26, v27, v28] using sq9Newpart7_run ({s with memory := v10}) (v24) (v24) (w8) (w11) (w17) (v13) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h8 : runInstructions sq9Newpart8Program {s with pc := N 6934, memory := v10, stack := v28 :: v27 :: w11 :: v26 :: v25 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6944, memory := v10, stack := v33 :: v30 :: v25 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart8Model, v29, v30, v31, v32, v33] using sq9Newpart8_run ({s with memory := v10}) (v28) (v27) (w11) (v26) (v25) (v13) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h9 : runInstructions sq9Newpart9Program {s with pc := N 6944, memory := v10, stack := v33 :: v30 :: v25 :: v13 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6954, memory := v10, stack := v38 :: v37 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart9Model, v34, v35, v36, v37, v38] using sq9Newpart9_run ({s with memory := v10}) (v33) (v30) (v25) (v13) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h10 : runInstructions sq9Newpart10Program {s with pc := N 6954, memory := v10, stack := v38 :: v37 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6963, memory := v10, stack := v43 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart10Model, v39, v40, v41, v42, v43] using sq9Newpart10_run ({s with memory := v10}) (v38) (v37) (v36) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h11 : runInstructions sq9Newpart11Program {s with pc := N 6963, memory := v10, stack := v43 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6972, memory := v10, stack := v47 :: w5 :: v46 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart11Model, v44, v45, v46, v47] using sq9Newpart11_run ({s with memory := v10}) (v43) (v36) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  have h12 : runInstructions sq9Newpart12Program {s with pc := N 6972, memory := v10, stack := v47 :: w5 :: v46 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} = some {s with pc := N 6976, memory := v10, stack := v14 :: w9 :: v49 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest} := by
    simpa only [sq9Newpart12Model, v48, v49] using sq9Newpart12_run ({s with memory := v10}) (v47) (w5) (v46) (v36) (w4) (w5) (w6) (w7) (v14) (w9) (w10) (w11) (w12) (v15) (w14) (w15) (w16) (w17) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))

#print axioms sq9New_run

def squareColumn9Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod carry w0 w1
  let v1 : W := v0 + w2
  let v2 : W := UInt256.mulMod w7 w16 w11
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 1280
  let v5 : W := UInt256.mulMod v4 w4 w11
  let v6 : W := v5 + v3
  let v7 : W := UInt256.mulMod w15 w13 w11
  let v8 : W := v7 + v6
  let v9 : W := UInt256.land w14 w3
  let v10 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v9.toNat 32) 768
  let v11 : W := v8 - v9
  let v12 : W := w11 + v11
  let v13 : W := UInt256.mulMod v12 (N 2048) w11
  let v14 : W := MachineState.readWord v10 1216
  let v15 : W := MachineState.readWord v10 1280
  let v16 : W := w17 * w8
  let v17 : W := MachineState.readWord v10 160
  let v18 : W := MachineState.readWord v10 32
  let v19 : W := v18 * v17
  let v20 : W := v19 + v16
  let v21 : W := MachineState.readWord v10 128
  let v22 : W := MachineState.readWord v10 64
  let v23 : W := v22 * v21
  let v24 : W := v23 + v20
  let v25 : W := v24 + v24
  let v26 : W := UInt256.mulMod w17 w8 w11
  let v27 : W := MachineState.readWord v10 160
  let v28 : W := MachineState.readWord v10 32
  let v29 : W := UInt256.mulMod v28 v27 w11
  let v30 : W := v29 + v26
  let v31 : W := MachineState.readWord v10 128
  let v32 : W := MachineState.readWord v10 64
  let v33 : W := UInt256.mulMod v32 v31 w11
  let v34 : W := v33 + v30
  let v35 : W := v34 + v34
  let v36 : W := v13 + v35
  let v37 : W := v13 + v25
  let v38 : W := MachineState.readWord v10 96
  let v39 : W := v38 * v38
  let v40 : W := v39 + v37
  let v41 : W := MachineState.readWord v10 192
  let v42 : W := w12 * v41
  let v43 : W := v42 + v40
  let v44 : W := MachineState.readWord v10 0
  let v45 : W := w10 * v44
  let v46 : W := v45 + v43
  let v47 : W := MachineState.readWord v10 224
  let v48 : W := v47 * w5
  let v49 : W := v48 + v46
  {s with pc := N 6976, memory := v10, stack := v14 :: w9 :: v49 :: v36 :: w4 :: w5 :: w6 :: w7 :: v14 :: w9 :: w10 :: w11 :: w12 :: v15 :: w14 :: w15 :: w16 :: w17 :: rest}

def squareColumn9Program : List Instr := sq9NewProgram

private theorem aux_shared0 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 768) 1280) = (MachineState.readWord s.memory 1280) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (w11 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w11) = (UInt256.mulMod z0 (N 2048) w11) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W) :
    squareColumn9Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest = sq9NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest := by
  let o0 : W := UInt256.mulMod carry w0 w1
  let o1 : W := o0 + w2
  let o2 : W := UInt256.mulMod w7 w16 w11
  let o3 : W := o2 + o1
  let o4 : W := MachineState.readWord s.memory 1280
  let o5 : W := UInt256.mulMod o4 w4 w11
  let o6 : W := o5 + o3
  let o7 : W := UInt256.mulMod w15 w13 w11
  let o8 : W := o7 + o6
  let o9 : W := UInt256.land w14 w3
  let o10 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o9.toNat 32) 768
  let o11 : W := o8 - o9
  let o12 : W := w11 + o11
  let o13 : W := UInt256.mulMod o12 (N 2048) w11
  let o14 : W := MachineState.readWord o10 1216
  let o15 : W := MachineState.readWord o10 1280
  let o16 : W := w17 * w8
  let o17 : W := MachineState.readWord o10 160
  let o18 : W := MachineState.readWord o10 32
  let o19 : W := o18 * o17
  let o20 : W := o19 + o16
  let o21 : W := MachineState.readWord o10 128
  let o22 : W := MachineState.readWord o10 64
  let o23 : W := o22 * o21
  let o24 : W := o23 + o20
  let o25 : W := o24 + o24
  let o26 : W := UInt256.mulMod w17 w8 w11
  let o27 : W := MachineState.readWord o10 160
  let o28 : W := MachineState.readWord o10 32
  let o29 : W := UInt256.mulMod o28 o27 w11
  let o30 : W := o29 + o26
  let o31 : W := MachineState.readWord o10 128
  let o32 : W := MachineState.readWord o10 64
  let o33 : W := UInt256.mulMod o32 o31 w11
  let o34 : W := o33 + o30
  let o35 : W := o34 + o34
  let o36 : W := o13 + o35
  let o37 : W := o13 + o25
  let o38 : W := MachineState.readWord o10 96
  let o39 : W := o38 * o38
  let o40 : W := o39 + o37
  let o41 : W := MachineState.readWord o10 192
  let o42 : W := w12 * o41
  let o43 : W := o42 + o40
  let o44 : W := MachineState.readWord o10 0
  let o45 : W := w10 * o44
  let o46 : W := o45 + o43
  let o47 : W := MachineState.readWord o10 224
  let o48 : W := o47 * w5
  let o49 : W := o48 + o46
  let n0 : W := UInt256.mulMod carry w0 w1
  let n1 : W := n0 + w2
  let n2 : W := UInt256.mulMod w7 w16 w11
  let n3 : W := n2 + n1
  let n4 : W := MachineState.readWord s.memory 1280
  let n5 : W := UInt256.mulMod n4 w4 w11
  let n6 : W := n5 + n3
  let n7 : W := UInt256.mulMod w15 w13 w11
  let n8 : W := n7 + n6
  let n9 : W := UInt256.land w14 w3
  let n10 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n9.toNat 32) 768
  let n11 : W := n8 - n9
  let n12 : W := w11 + n11
  let n13 : W := UInt256.mulMod (N 2048) n12 w11
  let n14 : W := MachineState.readWord n10 1216
  let n15 : W := MachineState.readWord n10 1280
  let n16 : W := w17 * w8
  let n17 : W := MachineState.readWord n10 160
  let n18 : W := MachineState.readWord n10 32
  let n19 : W := n18 * n17
  let n20 : W := n19 + n16
  let n21 : W := MachineState.readWord n10 128
  let n22 : W := MachineState.readWord n10 64
  let n23 : W := n22 * n21
  let n24 : W := n23 + n20
  let n25 : W := n24 + n24
  let n26 : W := UInt256.mulMod w17 w8 w11
  let n27 : W := MachineState.readWord n10 160
  let n28 : W := MachineState.readWord n10 32
  let n29 : W := UInt256.mulMod n28 n27 w11
  let n30 : W := n29 + n26
  let n31 : W := MachineState.readWord n10 128
  let n32 : W := MachineState.readWord n10 64
  let n33 : W := UInt256.mulMod n32 n31 w11
  let n34 : W := n33 + n30
  let n35 : W := n34 + n34
  let n36 : W := n13 + n35
  let n37 : W := n13 + n25
  let n38 : W := MachineState.readWord n10 96
  let n39 : W := n38 * n38
  let n40 : W := n39 + n37
  let n41 : W := MachineState.readWord n10 192
  let n42 : W := w12 * n41
  let n43 : W := n42 + n40
  let n44 : W := MachineState.readWord n10 0
  let n45 : W := w10 * n44
  let n46 : W := n45 + n43
  let n47 : W := MachineState.readWord n10 224
  let n48 : W := n47 * w5
  let n49 : W := n48 + n46
  have eq_o15 : o15 = o4 := by
    simpa only [o15, o10, o4] using
      (aux_shared0 s  o9)
  have eq_o27 : o27 = o17 := by
    simp only [o27, o17]
  have eq_o28 : o28 = o18 := by
    simp only [o28, o18]
  have eq_o31 : o31 = o21 := by
    simp only [o31, o21]
  have eq_o32 : o32 = o22 := by
    simp only [o32, o22]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2, eq_n1]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n3]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7, eq_n6]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n8, eq_n9]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11]
  have eq_n13 : n13 = o13 := by
    simpa only [n13, o13, eq_n12] using
      (aux_shared1 w11 o12)
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n10]
  have eq_n15 : n15 = o4 := by
    simpa only [n15, n10, o4, eq_n9] using
      (aux_shared0 s  o9)
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n10]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n10]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18, eq_n17]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n19, eq_n16]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n10]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n10]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22, eq_n21]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_n20]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26]
  have eq_n27 : n27 = o17 := by
    simp only [n27, o17, eq_n10]
  have eq_n28 : n28 = o18 := by
    simp only [n28, o18, eq_n10]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n28, eq_n27, eq_o28, eq_o27]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29, eq_n26]
  have eq_n31 : n31 = o21 := by
    simp only [n31, o21, eq_n10]
  have eq_n32 : n32 = o22 := by
    simp only [n32, o22, eq_n10]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32, eq_n31, eq_o32, eq_o31]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33, eq_n30]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n13, eq_n35]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n13, eq_n25]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n10]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n39, eq_n37]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n10]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42, eq_n40]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n10]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n44]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n45, eq_n43]
  have eq_n47 : n47 = o47 := by
    simp only [n47, o47, eq_n10]
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48, eq_n47]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49, eq_n48, eq_n46]
  change {s with pc := N 6976, memory := o10, stack := o14 :: w9 :: o49 :: o36 :: w4 :: w5 :: w6 :: w7 :: o14 :: w9 :: w10 :: w11 :: w12 :: o15 :: w14 :: w15 :: w16 :: w17 :: rest} =
    {s with pc := N 6976, memory := n10, stack := n14 :: w9 :: n49 :: n36 :: w4 :: w5 :: w6 :: w7 :: n14 :: w9 :: w10 :: w11 :: w12 :: n15 :: w14 :: w15 :: w16 :: w17 :: rest}
  simp only [eq_o15, eq_o27, eq_o28, eq_o31, eq_o32, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49]
theorem squareColumn9_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9Program {s with pc := N 6848, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: rest} =
      some (squareColumn9Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest) := by
  exact (sq9New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 rest).symm)

#print axioms squareColumn9_run
end CycleSubmission.Execution
