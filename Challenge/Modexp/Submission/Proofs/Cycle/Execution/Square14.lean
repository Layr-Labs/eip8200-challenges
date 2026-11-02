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

def sq14Newpart0Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 160,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def sq14Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 800
  let v1 : W := MachineState.readWord s.memory 160
  {s with pc := N 7510, memory := s.memory, stack := x8 :: v1 :: x14 :: x0 :: x1 :: x2 :: x3 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem sq14Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart0Program {s with pc := N 7498, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (sq14Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha800 : (800 : W).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq14Newpart0Program, sq14Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha800, hf800]


def sq14Newpart1Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩)]

def sq14Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x2 x1 x0
  let v1 : W := v0 + v0
  let v2 : W := x2 * x1
  {s with pc := N 7518, memory := s.memory, stack := v2 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq14Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart1Program {s with pc := N 7510, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq14Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart1Program, sq14Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart2Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq14Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + v0
  let v2 : W := x13 * x12
  let v3 : W := v2 + v1
  {s with pc := N 7526, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq14Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart2Program {s with pc := N 7518, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq14Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart2Program, sq14Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart3Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩)]

def sq14Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x15 * x0
  let v1 : W := v0 + x1
  let v2 : W := x3 + x2
  {s with pc := N 7534, memory := s.memory, stack := x13 :: x12 :: x11 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq14Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart3Program {s with pc := N 7526, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq14Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart3Program, sq14Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def sq14Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x11 x16 x12
  let v3 : W := v2 + v1
  {s with pc := N 7542, memory := s.memory, stack := x4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq14Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart4Program {s with pc := N 7534, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq14Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart4Program, sq14Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart5Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB]

def sq14Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x12 x0
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 128
  let v2 : W := x1 - v0
  {s with pc := N 7551, memory := v1, stack := v2 :: x9 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq14Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart5Program {s with pc := N 7542, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq14Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq14Newpart5Program, sq14Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def sq14Newpart6Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def sq14Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 + x0
  let v1 : W := UInt256.mulMod (N 2048) v0 x1
  {s with pc := N 7567, memory := s.memory, stack := x10 :: x9 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v1 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq14Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart6Program {s with pc := N 7551, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq14Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart6Program, sq14Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart7Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD]

def sq14Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x13 x0 x1
  let v1 : W := UInt256.mulMod x15 x15 x9
  let v2 : W := x11 + v1
  {s with pc := N 7575, memory := s.memory, stack := v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq14Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart7Program {s with pc := N 7567, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq14Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart7Program, sq14Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart8Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 3 1376,
   .op .MLOAD]

def sq14Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x13 * x10
  let v2 : W := x15 * x15
  let v3 : W := MachineState.readWord s.memory 1376
  {s with pc := N 7587, memory := s.memory, stack := v3 :: v2 :: v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq14Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart8Program {s with pc := N 7575, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq14Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1376 : (1376 : W).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq14Newpart8Program, sq14Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1376, hf1376]


def sq14Newpart9Program : List Instr :=
  [.op (.Swap ⟨12, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 160,
   .op .MSTORE]

def sq14Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x13 + x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.land x14 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 160
  {s with pc := N 7596, memory := v3, stack := v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x0 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq14Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart9Program {s with pc := N 7587, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq14Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq14Newpart9Program, sq14Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def sq14Newpart10Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Swap ⟨13, by decide⟩)]

def sq14Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x9
  {s with pc := N 7612, memory := s.memory, stack := x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: v2 :: rest}

theorem sq14Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart10Program {s with pc := N 7596, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq14Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq14Newpart10Program, sq14Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq14Newpart11Program : List Instr :=
  [.op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP]

def sq14Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1344
  {s with pc := N 7619, memory := s.memory, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v0 :: x13 :: x14 :: rest}

theorem sq14Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14Newpart11Program {s with pc := N 7612, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (sq14Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  have ha1344 : (1344 : W).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq14Newpart11Program, sq14Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1344, hf1344]


def sq14NewProgram : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 160,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 3 1376,
   .op .MLOAD,
   .op (.Swap ⟨12, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 160,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP]

def sq14NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 800
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := UInt256.mulMod w13 v1 w7
  let v3 : W := v2 + v2
  let v4 : W := w13 * v1
  let v5 : W := v4 + v4
  let v6 : W := carry + v5
  let v7 : W := w9 * w8
  let v8 : W := v7 + v6
  let v9 : W := w11 * w6
  let v10 : W := v9 + v8
  let v11 : W := carry + v3
  let v12 : W := UInt256.mulMod w9 w8 w7
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w6 w11 w7
  let v15 : W := v14 + v13
  let v16 : W := UInt256.land w10 v10
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 128
  let v18 : W := v15 - v16
  let v19 : W := w7 + v18
  let v20 : W := UInt256.mulMod (N 2048) v19 w7
  let v21 : W := UInt256.mulMod w11 w8 w7
  let v22 : W := UInt256.mulMod w13 w13 w7
  let v23 : W := v20 + v22
  let v24 : W := v23 + v21
  let v25 : W := w11 * w8
  let v26 : W := w13 * w13
  let v27 : W := MachineState.readWord v17 1376
  let v28 : W := v20 + v26
  let v29 : W := v28 + v25
  let v30 : W := UInt256.land w10 v29
  let v31 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v30.toNat 32) 160
  let v32 : W := v24 - v30
  let v33 : W := w7 + v32
  let v34 : W := UInt256.mulMod (N 2048) v33 w7
  let v35 : W := MachineState.readWord v31 1344
  {s with pc := N 7619, memory := v31, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v27 :: w10 :: v35 :: w12 :: v34 :: rest}

theorem sq14New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq14NewProgram {s with pc := N 7498, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (sq14NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  let v0 : W := MachineState.readWord s.memory 800
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := UInt256.mulMod w13 v1 w7
  let v3 : W := v2 + v2
  let v4 : W := w13 * v1
  let v5 : W := v4 + v4
  let v6 : W := carry + v5
  let v7 : W := w9 * w8
  let v8 : W := v7 + v6
  let v9 : W := w11 * w6
  let v10 : W := v9 + v8
  let v11 : W := carry + v3
  let v12 : W := UInt256.mulMod w9 w8 w7
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w6 w11 w7
  let v15 : W := v14 + v13
  let v16 : W := UInt256.land w10 v10
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 128
  let v18 : W := v15 - v16
  let v19 : W := w7 + v18
  let v20 : W := UInt256.mulMod (N 2048) v19 w7
  let v21 : W := UInt256.mulMod w11 w8 w7
  let v22 : W := UInt256.mulMod w13 w13 w7
  let v23 : W := v20 + v22
  let v24 : W := v23 + v21
  let v25 : W := w11 * w8
  let v26 : W := w13 * w13
  let v27 : W := MachineState.readWord v17 1376
  let v28 : W := v20 + v26
  let v29 : W := v28 + v25
  let v30 : W := UInt256.land w10 v29
  let v31 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v30.toNat 32) 160
  let v32 : W := v24 - v30
  let v33 : W := w7 + v32
  let v34 : W := UInt256.mulMod (N 2048) v33 w7
  let v35 : W := MachineState.readWord v31 1344
  have h0 : runInstructions sq14Newpart0Program {s with pc := N 7498, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7510, memory := s.memory, stack := w7 :: v1 :: w13 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart0Model, v0, v1] using sq14Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions sq14Newpart1Program {s with pc := N 7510, memory := s.memory, stack := w7 :: v1 :: w13 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7518, memory := s.memory, stack := v4 :: v4 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart1Model, v2, v3, v4] using sq14Newpart1_run (s) (w7) (v1) (w13) (carry) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions sq14Newpart2Program {s with pc := N 7518, memory := s.memory, stack := v4 :: v4 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7526, memory := s.memory, stack := w6 :: v8 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart2Model, v5, v6, v7, v8] using sq14Newpart2_run (s) (v4) (v4) (v3) (carry) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions sq14Newpart3Program {s with pc := N 7526, memory := s.memory, stack := w6 :: v8 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7534, memory := s.memory, stack := w9 :: w8 :: w7 :: v11 :: v10 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart3Model, v9, v10, v11] using sq14Newpart3_run (s) (w6) (v8) (v3) (carry) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h4 : runInstructions sq14Newpart4Program {s with pc := N 7534, memory := s.memory, stack := w9 :: w8 :: w7 :: v11 :: v10 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7542, memory := s.memory, stack := v10 :: v15 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart4Model, v12, v13, v14, v15] using sq14Newpart4_run (s) (w9) (w8) (w7) (v11) (v10) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h5 : runInstructions sq14Newpart5Program {s with pc := N 7542, memory := s.memory, stack := v10 :: v15 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7551, memory := v17, stack := v18 :: w7 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart5Model, v16, v17, v18] using sq14Newpart5_run (s) (v10) (v15) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h6 : runInstructions sq14Newpart6Program {s with pc := N 7551, memory := v17, stack := v18 :: w7 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7567, memory := v17, stack := w8 :: w7 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v20 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart6Model, v19, v20] using sq14Newpart6_run ({s with memory := v17}) (v18) (w7) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h7 : runInstructions sq14Newpart7Program {s with pc := N 7567, memory := v17, stack := w8 :: w7 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v20 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7575, memory := v17, stack := v23 :: v21 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v20 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart7Model, v21, v22, v23] using sq14Newpart7_run ({s with memory := v17}) (w8) (w7) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v20) (w10) (w11) (w12) (w13) rest hcap hact
  have h8 : runInstructions sq14Newpart8Program {s with pc := N 7575, memory := v17, stack := v23 :: v21 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v20 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7587, memory := v17, stack := v27 :: v26 :: v25 :: v24 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v20 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart8Model, v24, v25, v26, v27] using sq14Newpart8_run ({s with memory := v17}) (v23) (v21) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v20) (w10) (w11) (w12) (w13) rest hcap hact
  have h9 : runInstructions sq14Newpart9Program {s with pc := N 7587, memory := v17, stack := v27 :: v26 :: v25 :: v24 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v20 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7596, memory := v31, stack := v30 :: v24 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v27 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [sq14Newpart9Model, v28, v29, v30, v31] using sq14Newpart9_run ({s with memory := v17}) (v27) (v26) (v25) (v24) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v20) (w10) (w11) (w12) (w13) rest hcap hact
  have h10 : runInstructions sq14Newpart10Program {s with pc := N 7596, memory := v31, stack := v30 :: v24 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v27 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7612, memory := v31, stack := w13 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v27 :: w10 :: w11 :: w12 :: v34 :: rest} := by
    simpa only [sq14Newpart10Model, v32, v33, v34] using sq14Newpart10_run ({s with memory := v31}) (v30) (v24) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v27) (w10) (w11) (w12) (w13) rest hcap hact
  have h11 : runInstructions sq14Newpart11Program {s with pc := N 7612, memory := v31, stack := w13 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v27 :: w10 :: w11 :: w12 :: v34 :: rest} = some {s with pc := N 7619, memory := v31, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v27 :: w10 :: v35 :: w12 :: v34 :: rest} := by
    simpa only [sq14Newpart11Model, v35] using sq14Newpart11_run ({s with memory := v31}) (w13) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v27) (w10) (w11) (w12) (v34) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

#print axioms sq14New_run

def squareColumn14Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 800
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := w13 * v1
  let v3 : W := v2 + v2
  let v4 : W := UInt256.mulMod w13 v1 w7
  let v5 : W := v4 + v4
  let v6 : W := carry + v5
  let v7 : W := carry + v3
  let v8 : W := w8 * w9
  let v9 : W := v8 + v7
  let v10 : W := w6 * w11
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w8 w9 w7
  let v13 : W := v12 + v6
  let v14 : W := UInt256.mulMod w6 w11 w7
  let v15 : W := v14 + v13
  let v16 : W := UInt256.land w10 v11
  let v17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v16.toNat 32) 128
  let v18 : W := v15 - v16
  let v19 : W := w7 + v18
  let v20 : W := UInt256.mulMod v19 (N 2048) w7
  let v21 : W := MachineState.readWord v17 1376
  let v22 : W := UInt256.mulMod w13 w13 w7
  let v23 : W := w13 * w13
  let v24 : W := v20 + v23
  let v25 : W := w11 * w8
  let v26 : W := v25 + v24
  let v27 : W := v20 + v22
  let v28 : W := UInt256.mulMod w8 w11 w7
  let v29 : W := v28 + v27
  let v30 : W := UInt256.land w10 v26
  let v31 : ByteArray := MachineState.writeBytes v17 (Data.Bytes.natToBytesPadded v30.toNat 32) 160
  let v32 : W := v29 - v30
  let v33 : W := w7 + v32
  let v34 : W := UInt256.mulMod v33 (N 2048) w7
  let v35 : W := MachineState.readWord v31 1344
  {s with pc := N 7619, memory := v31, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v21 :: w10 :: v35 :: w12 :: v34 :: rest}

def squareColumn14Program : List Instr := sq14NewProgram

private theorem aux_shared0 (w8 w9 : W) :
    (w9 * w8) = (w8 * w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (w6 w11 : W) :
    (w11 * w6) = (w6 * w11) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (w7 w8 w9 : W) :
    (UInt256.mulMod w9 w8 w7) = (UInt256.mulMod w8 w9 w7) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (w7 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w7) = (UInt256.mulMod z0 (N 2048) w7) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (w7 w8 w11 : W) :
    (UInt256.mulMod w11 w8 w7) = (UInt256.mulMod w8 w11 w7) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared5 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W) :
    squareColumn14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest = sq14NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest := by
  let o0 : W := MachineState.readWord s.memory 800
  let o1 : W := MachineState.readWord s.memory 160
  let o2 : W := w13 * o1
  let o3 : W := o2 + o2
  let o4 : W := UInt256.mulMod w13 o1 w7
  let o5 : W := o4 + o4
  let o6 : W := carry + o5
  let o7 : W := carry + o3
  let o8 : W := w8 * w9
  let o9 : W := o8 + o7
  let o10 : W := w6 * w11
  let o11 : W := o10 + o9
  let o12 : W := UInt256.mulMod w8 w9 w7
  let o13 : W := o12 + o6
  let o14 : W := UInt256.mulMod w6 w11 w7
  let o15 : W := o14 + o13
  let o16 : W := UInt256.land w10 o11
  let o17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o16.toNat 32) 128
  let o18 : W := o15 - o16
  let o19 : W := w7 + o18
  let o20 : W := UInt256.mulMod o19 (N 2048) w7
  let o21 : W := MachineState.readWord o17 1376
  let o22 : W := UInt256.mulMod w13 w13 w7
  let o23 : W := w13 * w13
  let o24 : W := o20 + o23
  let o25 : W := w11 * w8
  let o26 : W := o25 + o24
  let o27 : W := o20 + o22
  let o28 : W := UInt256.mulMod w8 w11 w7
  let o29 : W := o28 + o27
  let o30 : W := UInt256.land w10 o26
  let o31 : ByteArray := MachineState.writeBytes o17 (Data.Bytes.natToBytesPadded o30.toNat 32) 160
  let o32 : W := o29 - o30
  let o33 : W := w7 + o32
  let o34 : W := UInt256.mulMod o33 (N 2048) w7
  let o35 : W := MachineState.readWord o31 1344
  let n0 : W := MachineState.readWord s.memory 800
  let n1 : W := MachineState.readWord s.memory 160
  let n2 : W := UInt256.mulMod w13 n1 w7
  let n3 : W := n2 + n2
  let n4 : W := w13 * n1
  let n5 : W := n4 + n4
  let n6 : W := carry + n5
  let n7 : W := w9 * w8
  let n8 : W := n7 + n6
  let n9 : W := w11 * w6
  let n10 : W := n9 + n8
  let n11 : W := carry + n3
  let n12 : W := UInt256.mulMod w9 w8 w7
  let n13 : W := n12 + n11
  let n14 : W := UInt256.mulMod w6 w11 w7
  let n15 : W := n14 + n13
  let n16 : W := UInt256.land w10 n10
  let n17 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n16.toNat 32) 128
  let n18 : W := n15 - n16
  let n19 : W := w7 + n18
  let n20 : W := UInt256.mulMod (N 2048) n19 w7
  let n21 : W := UInt256.mulMod w11 w8 w7
  let n22 : W := UInt256.mulMod w13 w13 w7
  let n23 : W := n20 + n22
  let n24 : W := n23 + n21
  let n25 : W := w11 * w8
  let n26 : W := w13 * w13
  let n27 : W := MachineState.readWord n17 1376
  let n28 : W := n20 + n26
  let n29 : W := n28 + n25
  let n30 : W := UInt256.land w10 n29
  let n31 : ByteArray := MachineState.writeBytes n17 (Data.Bytes.natToBytesPadded n30.toNat 32) 160
  let n32 : W := n24 - n30
  let n33 : W := w7 + n32
  let n34 : W := UInt256.mulMod (N 2048) n33 w7
  let n35 : W := MachineState.readWord n31 1344
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1]
  have eq_n2 : n2 = o4 := by
    simp only [n2, o4, eq_n1]
  have eq_n3 : n3 = o5 := by
    simp only [n3, o5, eq_n2]
  have eq_n4 : n4 = o2 := by
    simp only [n4, o2, eq_n1]
  have eq_n5 : n5 = o3 := by
    simp only [n5, o3, eq_n4]
  have eq_n6 : n6 = o7 := by
    simp only [n6, o7, eq_n5]
  have eq_n7 : n7 = o8 := by
    simpa only [n7, o8] using
      (aux_shared0 w8 w9 )
  have eq_n8 : n8 = o9 := by
    simp only [n8, o9, eq_n7, eq_n6]
  have eq_n9 : n9 = o10 := by
    simpa only [n9, o10] using
      (aux_shared1 w6 w11 )
  have eq_n10 : n10 = o11 := by
    simp only [n10, o11, eq_n9, eq_n8]
  have eq_n11 : n11 = o6 := by
    simp only [n11, o6, eq_n3]
  have eq_n12 : n12 = o12 := by
    simpa only [n12, o12] using
      (aux_shared2 w7 w8 w9 )
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n12, eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14, eq_n13]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16, eq_n10]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n16]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n15, eq_n16]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18]
  have eq_n20 : n20 = o20 := by
    simpa only [n20, o20, eq_n19] using
      (aux_shared3 w7 o19)
  have eq_n21 : n21 = o28 := by
    simpa only [n21, o28] using
      (aux_shared4 w7 w8 w11 )
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22]
  have eq_n23 : n23 = o27 := by
    simp only [n23, o27, eq_n20, eq_n22]
  have eq_n24 : n24 = o29 := by
    simpa only [n24, o29, eq_n23, eq_n21] using
      (aux_shared5  o27 o28)
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25]
  have eq_n26 : n26 = o23 := by
    simp only [n26, o23]
  have eq_n27 : n27 = o21 := by
    simp only [n27, o21, eq_n17]
  have eq_n28 : n28 = o24 := by
    simp only [n28, o24, eq_n20, eq_n26]
  have eq_n29 : n29 = o26 := by
    simpa only [n29, o26, eq_n28, eq_n25] using
      (aux_shared5  o24 o25)
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n17, eq_n30]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n24, eq_n30]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32]
  have eq_n34 : n34 = o34 := by
    simpa only [n34, o34, eq_n33] using
      (aux_shared3 w7 o33)
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n31]
  change {s with pc := N 7619, memory := o31, stack := w0 :: w1 :: w2 :: o0 :: w4 :: w5 :: w6 :: w7 :: w8 :: o21 :: w10 :: o35 :: w12 :: o34 :: rest} =
    {s with pc := N 7619, memory := n31, stack := w0 :: w1 :: w2 :: n0 :: w4 :: w5 :: w6 :: w7 :: w8 :: n27 :: w10 :: n35 :: w12 :: n34 :: rest}
  simp only [eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35]
theorem squareColumn14_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14Program {s with pc := N 7498, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (squareColumn14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  exact (sq14New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest).symm)

#print axioms squareColumn14_run
end CycleSubmission.Execution
