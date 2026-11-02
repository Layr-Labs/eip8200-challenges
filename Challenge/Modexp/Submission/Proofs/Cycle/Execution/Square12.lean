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

def sq12Newpart0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq12Newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := x11 * v2
  let v4 : W := v3 + v1
  {s with pc := N 7244, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart0Program {s with pc := N 7235, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart0Program, sq12Newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def sq12Newpart1Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq12Newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x8 * x6
  let v1 : W := v0 + x0
  let v2 : W := x5 * x3
  let v3 : W := v2 + v1
  {s with pc := N 7252, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq12Newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart1Program {s with pc := N 7244, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq12Newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart1Program, sq12Newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12Newpart2Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD]

def sq12Newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x7 * x11
  let v1 : W := v0 + x0
  let v2 : W := x13 * x4
  let v3 : W := v2 + v1
  {s with pc := N 7260, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq12Newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart2Program {s with pc := N 7252, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq12Newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart2Program, sq12Newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12Newpart3Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq12Newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := UInt256.mulMod v0 v0 x9
  let v2 : W := v1 + x1
  {s with pc := N 7269, memory := s.memory, stack := x9 :: v2 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem sq12Newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart3Program {s with pc := N 7260, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (sq12Newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart3Program, sq12Newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def sq12Newpart4Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def sq12Newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := UInt256.mulMod x11 v0 x0
  let v2 : W := v1 + x1
  {s with pc := N 7278, memory := s.memory, stack := x9 :: x7 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart4Program {s with pc := N 7269, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart4Program, sq12Newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def sq12Newpart5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def sq12Newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x8 x6 x12
  let v3 : W := v2 + v1
  {s with pc := N 7286, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq12Newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart5Program {s with pc := N 7278, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq12Newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart5Program, sq12Newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12Newpart6Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD]

def sq12Newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x12 x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x14 x5 x10
  {s with pc := N 7294, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart6Program {s with pc := N 7286, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart6Program, sq12Newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12Newpart7Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 32,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩)]

def sq12Newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.land x13 x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 32
  {s with pc := N 7303, memory := v2, stack := x10 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart7Program {s with pc := N 7294, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart7Program, sq12Newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]


def sq12Newpart8Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def sq12Newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x2 - x1
  let v1 : W := x0 + v0
  let v2 : W := UInt256.mulMod (N 2048) v1 x0
  {s with pc := N 7319, memory := s.memory, stack := x10 :: x16 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart8Program {s with pc := N 7303, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart8Program, sq12Newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12Newpart9Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 128,
   .op .MLOAD]

def sq12Newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := x1 * v0
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := MachineState.readWord s.memory 128
  {s with pc := N 7331, memory := s.memory, stack := v3 :: v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart9Program {s with pc := N 7319, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart9Program, sq12Newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha128, hf128, ha160, hf160]


def sq12Newpart10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def sq12Newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := v1 + v1
  let v3 : W := UInt256.mulMod x5 x3 x4
  let v4 : W := MachineState.readWord s.memory 160
  {s with pc := N 7341, memory := s.memory, stack := v4 :: x14 :: v3 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem sq12Newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart10Program {s with pc := N 7331, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (sq12Newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart10Program, sq12Newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def sq12Newpart11Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD]

def sq12Newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := UInt256.mulMod v0 x0 x1
  let v2 : W := v1 + x2
  let v3 : W := v2 + v2
  let v4 : W := x4 + v3
  {s with pc := N 7350, memory := s.memory, stack := v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem sq12Newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart11Program {s with pc := N 7341, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (sq12Newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, sq12Newpart11Program, sq12Newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def sq12Newpart12Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def sq12Newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x2 + x1
  let v1 : W := x11 * x7
  let v2 : W := v1 + v0
  {s with pc := N 7358, memory := s.memory, stack := x9 :: x6 :: v2 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem sq12Newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart12Program {s with pc := N 7350, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (sq12Newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart12Program, sq12Newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12Newpart13Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL]

def sq12Newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x5 * x13
  {s with pc := N 7363, memory := s.memory, stack := v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem sq12Newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12Newpart13Program {s with pc := N 7358, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (sq12Newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, sq12Newpart13Program, sq12Newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def sq12NewProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 32,
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
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 128,
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
   .push 1 128,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL]

def sq12NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry * carry
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := w10 * v2
  let v4 : W := v3 + v1
  let v5 : W := w8 * w6
  let v6 : W := v5 + v4
  let v7 : W := w5 * w3
  let v8 : W := v7 + v6
  let v9 : W := w7 * w11
  let v10 : W := v9 + v8
  let v11 : W := w13 * w4
  let v12 : W := v11 + v10
  let v13 : W := MachineState.readWord s.memory 128
  let v14 : W := UInt256.mulMod v13 v13 w9
  let v15 : W := v14 + w1
  let v16 : W := MachineState.readWord s.memory 224
  let v17 : W := UInt256.mulMod w10 v16 w9
  let v18 : W := v17 + v15
  let v19 : W := UInt256.mulMod w8 w6 w9
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod w5 w3 w9
  let v22 : W := v21 + v20
  let v23 : W := UInt256.mulMod w7 w11 w9
  let v24 : W := v23 + v22
  let v25 : W := UInt256.mulMod w13 w4 w9
  let v26 : W := v25 + v24
  let v27 : W := UInt256.land w12 v12
  let v28 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v27.toNat 32) 32
  let v29 : W := v26 - v27
  let v30 : W := w9 + v29
  let v31 : W := UInt256.mulMod (N 2048) v30 w9
  let v32 : W := MachineState.readWord v28 96
  let v33 : W := w15 * v32
  let v34 : W := MachineState.readWord v28 160
  let v35 : W := MachineState.readWord v28 128
  let v36 : W := v35 * v34
  let v37 : W := v36 + v33
  let v38 : W := v37 + v37
  let v39 : W := UInt256.mulMod w15 v32 w9
  let v40 : W := MachineState.readWord v28 160
  let v41 : W := MachineState.readWord v28 128
  let v42 : W := UInt256.mulMod v41 v40 w9
  let v43 : W := v42 + v39
  let v44 : W := v43 + v43
  let v45 : W := v31 + v44
  let v46 : W := v31 + v38
  let v47 : W := w10 * w6
  let v48 : W := v47 + v46
  let v49 : W := w8 * w5
  let v50 : W := v49 + v48
  let v51 : W := w3 * w11
  {s with pc := N 7363, memory := v28, stack := v51 :: v50 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem sq12New_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions sq12NewProgram {s with pc := N 7235, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (sq12NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := carry * carry
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := w10 * v2
  let v4 : W := v3 + v1
  let v5 : W := w8 * w6
  let v6 : W := v5 + v4
  let v7 : W := w5 * w3
  let v8 : W := v7 + v6
  let v9 : W := w7 * w11
  let v10 : W := v9 + v8
  let v11 : W := w13 * w4
  let v12 : W := v11 + v10
  let v13 : W := MachineState.readWord s.memory 128
  let v14 : W := UInt256.mulMod v13 v13 w9
  let v15 : W := v14 + w1
  let v16 : W := MachineState.readWord s.memory 224
  let v17 : W := UInt256.mulMod w10 v16 w9
  let v18 : W := v17 + v15
  let v19 : W := UInt256.mulMod w8 w6 w9
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod w5 w3 w9
  let v22 : W := v21 + v20
  let v23 : W := UInt256.mulMod w7 w11 w9
  let v24 : W := v23 + v22
  let v25 : W := UInt256.mulMod w13 w4 w9
  let v26 : W := v25 + v24
  let v27 : W := UInt256.land w12 v12
  let v28 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v27.toNat 32) 32
  let v29 : W := v26 - v27
  let v30 : W := w9 + v29
  let v31 : W := UInt256.mulMod (N 2048) v30 w9
  let v32 : W := MachineState.readWord v28 96
  let v33 : W := w15 * v32
  let v34 : W := MachineState.readWord v28 160
  let v35 : W := MachineState.readWord v28 128
  let v36 : W := v35 * v34
  let v37 : W := v36 + v33
  let v38 : W := v37 + v37
  let v39 : W := UInt256.mulMod w15 v32 w9
  let v40 : W := MachineState.readWord v28 160
  let v41 : W := MachineState.readWord v28 128
  let v42 : W := UInt256.mulMod v41 v40 w9
  let v43 : W := v42 + v39
  let v44 : W := v43 + v43
  let v45 : W := v31 + v44
  let v46 : W := v31 + v38
  let v47 : W := w10 * w6
  let v48 : W := v47 + v46
  let v49 : W := w8 * w5
  let v50 : W := v49 + v48
  let v51 : W := w3 * w11
  have h0 : runInstructions sq12Newpart0Program {s with pc := N 7235, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7244, memory := s.memory, stack := v4 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart0Model, v0, v1, v2, v3, v4] using sq12Newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions sq12Newpart1Program {s with pc := N 7244, memory := s.memory, stack := v4 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7252, memory := s.memory, stack := v8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart1Model, v5, v6, v7, v8] using sq12Newpart1_run (s) (v4) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions sq12Newpart2Program {s with pc := N 7252, memory := s.memory, stack := v8 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7260, memory := s.memory, stack := v12 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart2Model, v9, v10, v11, v12] using sq12Newpart2_run (s) (v8) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions sq12Newpart3Program {s with pc := N 7260, memory := s.memory, stack := v12 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7269, memory := s.memory, stack := w9 :: v15 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart3Model, v13, v14, v15] using sq12Newpart3_run (s) (v12) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions sq12Newpart4Program {s with pc := N 7269, memory := s.memory, stack := w9 :: v15 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7278, memory := s.memory, stack := w8 :: w6 :: w9 :: v18 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart4Model, v16, v17, v18] using sq12Newpart4_run (s) (w9) (v15) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions sq12Newpart5Program {s with pc := N 7278, memory := s.memory, stack := w8 :: w6 :: w9 :: v18 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7286, memory := s.memory, stack := w9 :: v22 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart5Model, v19, v20, v21, v22] using sq12Newpart5_run (s) (w8) (w6) (w9) (v18) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions sq12Newpart6Program {s with pc := N 7286, memory := s.memory, stack := w9 :: v22 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7294, memory := s.memory, stack := v25 :: v24 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart6Model, v23, v24, v25] using sq12Newpart6_run (s) (w9) (v22) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h7 : runInstructions sq12Newpart7Program {s with pc := N 7294, memory := s.memory, stack := v25 :: v24 :: v12 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7303, memory := v28, stack := w9 :: v27 :: v26 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart7Model, v26, v27, v28] using sq12Newpart7_run (s) (v25) (v24) (v12) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h8 : runInstructions sq12Newpart8Program {s with pc := N 7303, memory := v28, stack := w9 :: v27 :: v26 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7319, memory := v28, stack := w9 :: w15 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart8Model, v29, v30, v31] using sq12Newpart8_run ({s with memory := v28}) (w9) (v27) (v26) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h9 : runInstructions sq12Newpart9Program {s with pc := N 7319, memory := v28, stack := w9 :: w15 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7331, memory := v28, stack := v35 :: v34 :: v33 :: v32 :: w9 :: w15 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart9Model, v32, v33, v34, v35] using sq12Newpart9_run ({s with memory := v28}) (w9) (w15) (v31) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h10 : runInstructions sq12Newpart10Program {s with pc := N 7331, memory := v28, stack := v35 :: v34 :: v33 :: v32 :: w9 :: w15 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7341, memory := v28, stack := v40 :: w9 :: v39 :: v38 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart10Model, v36, v37, v38, v39, v40] using sq12Newpart10_run ({s with memory := v28}) (v35) (v34) (v33) (v32) (w9) (w15) (v31) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h11 : runInstructions sq12Newpart11Program {s with pc := N 7341, memory := v28, stack := v40 :: w9 :: v39 :: v38 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7350, memory := v28, stack := v45 :: v38 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart11Model, v41, v42, v43, v44, v45] using sq12Newpart11_run ({s with memory := v28}) (v40) (w9) (v39) (v38) (v31) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h12 : runInstructions sq12Newpart12Program {s with pc := N 7350, memory := v28, stack := v45 :: v38 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7358, memory := v28, stack := w8 :: w5 :: v48 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart12Model, v46, v47, v48] using sq12Newpart12_run ({s with memory := v28}) (v45) (v38) (v31) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h13 : runInstructions sq12Newpart13Program {s with pc := N 7358, memory := v28, stack := w8 :: w5 :: v48 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7363, memory := v28, stack := v51 :: v50 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [sq12Newpart13Model, v49, v50, v51] using sq12Newpart13_run ({s with memory := v28}) (w8) (w5) (v48) (v45) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

#print axioms sq12New_run

def squareColumn12Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry * carry
  let v1 : W := v0 + w0
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := w10 * v2
  let v4 : W := v3 + v1
  let v5 : W := w8 * w6
  let v6 : W := v5 + v4
  let v7 : W := w5 * w3
  let v8 : W := v7 + v6
  let v9 : W := w7 * w11
  let v10 : W := v9 + v8
  let v11 : W := w13 * w4
  let v12 : W := v11 + v10
  let v13 : W := MachineState.readWord s.memory 128
  let v14 : W := UInt256.mulMod v13 v13 w9
  let v15 : W := v14 + w1
  let v16 : W := MachineState.readWord s.memory 224
  let v17 : W := UInt256.mulMod w10 v16 w9
  let v18 : W := v17 + v15
  let v19 : W := UInt256.mulMod w8 w6 w9
  let v20 : W := v19 + v18
  let v21 : W := UInt256.mulMod w5 w3 w9
  let v22 : W := v21 + v20
  let v23 : W := UInt256.mulMod w7 w11 w9
  let v24 : W := v23 + v22
  let v25 : W := UInt256.mulMod w13 w4 w9
  let v26 : W := v25 + v24
  let v27 : W := UInt256.land w12 v12
  let v28 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v27.toNat 32) 32
  let v29 : W := v26 - v27
  let v30 : W := w9 + v29
  let v31 : W := UInt256.mulMod v30 (N 2048) w9
  let v32 : W := MachineState.readWord v28 96
  let v33 : W := w15 * v32
  let v34 : W := MachineState.readWord v28 160
  let v35 : W := MachineState.readWord v28 128
  let v36 : W := v35 * v34
  let v37 : W := v36 + v33
  let v38 : W := v37 + v37
  let v39 : W := UInt256.mulMod w15 v32 w9
  let v40 : W := MachineState.readWord v28 160
  let v41 : W := MachineState.readWord v28 128
  let v42 : W := UInt256.mulMod v41 v40 w9
  let v43 : W := v42 + v39
  let v44 : W := v43 + v43
  let v45 : W := v31 + v44
  let v46 : W := v31 + v38
  let v47 : W := w10 * w6
  let v48 : W := v47 + v46
  let v49 : W := w8 * w5
  let v50 : W := v49 + v48
  let v51 : W := w3 * w11
  {s with pc := N 7363, memory := v28, stack := v51 :: v50 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

def squareColumn12Program : List Instr := sq12NewProgram

private theorem aux_shared0 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 32) 128) = (MachineState.readWord s.memory 128) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (w9 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w9) = (UInt256.mulMod z0 (N 2048) w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem prepared_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    squareColumn12Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = sq12NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := carry * carry
  let o1 : W := o0 + w0
  let o2 : W := MachineState.readWord s.memory 224
  let o3 : W := w10 * o2
  let o4 : W := o3 + o1
  let o5 : W := w8 * w6
  let o6 : W := o5 + o4
  let o7 : W := w5 * w3
  let o8 : W := o7 + o6
  let o9 : W := w7 * w11
  let o10 : W := o9 + o8
  let o11 : W := w13 * w4
  let o12 : W := o11 + o10
  let o13 : W := MachineState.readWord s.memory 128
  let o14 : W := UInt256.mulMod o13 o13 w9
  let o15 : W := o14 + w1
  let o16 : W := MachineState.readWord s.memory 224
  let o17 : W := UInt256.mulMod w10 o16 w9
  let o18 : W := o17 + o15
  let o19 : W := UInt256.mulMod w8 w6 w9
  let o20 : W := o19 + o18
  let o21 : W := UInt256.mulMod w5 w3 w9
  let o22 : W := o21 + o20
  let o23 : W := UInt256.mulMod w7 w11 w9
  let o24 : W := o23 + o22
  let o25 : W := UInt256.mulMod w13 w4 w9
  let o26 : W := o25 + o24
  let o27 : W := UInt256.land w12 o12
  let o28 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o27.toNat 32) 32
  let o29 : W := o26 - o27
  let o30 : W := w9 + o29
  let o31 : W := UInt256.mulMod o30 (N 2048) w9
  let o32 : W := MachineState.readWord o28 96
  let o33 : W := w15 * o32
  let o34 : W := MachineState.readWord o28 160
  let o35 : W := MachineState.readWord o28 128
  let o36 : W := o35 * o34
  let o37 : W := o36 + o33
  let o38 : W := o37 + o37
  let o39 : W := UInt256.mulMod w15 o32 w9
  let o40 : W := MachineState.readWord o28 160
  let o41 : W := MachineState.readWord o28 128
  let o42 : W := UInt256.mulMod o41 o40 w9
  let o43 : W := o42 + o39
  let o44 : W := o43 + o43
  let o45 : W := o31 + o44
  let o46 : W := o31 + o38
  let o47 : W := w10 * w6
  let o48 : W := o47 + o46
  let o49 : W := w8 * w5
  let o50 : W := o49 + o48
  let o51 : W := w3 * w11
  let n0 : W := carry * carry
  let n1 : W := n0 + w0
  let n2 : W := MachineState.readWord s.memory 224
  let n3 : W := w10 * n2
  let n4 : W := n3 + n1
  let n5 : W := w8 * w6
  let n6 : W := n5 + n4
  let n7 : W := w5 * w3
  let n8 : W := n7 + n6
  let n9 : W := w7 * w11
  let n10 : W := n9 + n8
  let n11 : W := w13 * w4
  let n12 : W := n11 + n10
  let n13 : W := MachineState.readWord s.memory 128
  let n14 : W := UInt256.mulMod n13 n13 w9
  let n15 : W := n14 + w1
  let n16 : W := MachineState.readWord s.memory 224
  let n17 : W := UInt256.mulMod w10 n16 w9
  let n18 : W := n17 + n15
  let n19 : W := UInt256.mulMod w8 w6 w9
  let n20 : W := n19 + n18
  let n21 : W := UInt256.mulMod w5 w3 w9
  let n22 : W := n21 + n20
  let n23 : W := UInt256.mulMod w7 w11 w9
  let n24 : W := n23 + n22
  let n25 : W := UInt256.mulMod w13 w4 w9
  let n26 : W := n25 + n24
  let n27 : W := UInt256.land w12 n12
  let n28 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n27.toNat 32) 32
  let n29 : W := n26 - n27
  let n30 : W := w9 + n29
  let n31 : W := UInt256.mulMod (N 2048) n30 w9
  let n32 : W := MachineState.readWord n28 96
  let n33 : W := w15 * n32
  let n34 : W := MachineState.readWord n28 160
  let n35 : W := MachineState.readWord n28 128
  let n36 : W := n35 * n34
  let n37 : W := n36 + n33
  let n38 : W := n37 + n37
  let n39 : W := UInt256.mulMod w15 n32 w9
  let n40 : W := MachineState.readWord n28 160
  let n41 : W := MachineState.readWord n28 128
  let n42 : W := UInt256.mulMod n41 n40 w9
  let n43 : W := n42 + n39
  let n44 : W := n43 + n43
  let n45 : W := n31 + n44
  let n46 : W := n31 + n38
  let n47 : W := w10 * w6
  let n48 : W := n47 + n46
  let n49 : W := w8 * w5
  let n50 : W := n49 + n48
  let n51 : W := w3 * w11
  have eq_o16 : o16 = o2 := by
    simp only [o16, o2]
  have eq_o35 : o35 = o13 := by
    simpa only [o35, o28, o13] using
      (aux_shared0 s  o27)
  have eq_o40 : o40 = o34 := by
    simp only [o40, o34]
  have eq_o41 : o41 = o13 := by
    simpa only [o41, o28, o13] using
      (aux_shared0 s  o27)
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3, eq_n1]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n4]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7, eq_n6]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9, eq_n8]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n10]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n13]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14]
  have eq_n16 : n16 = o2 := by
    simp only [n16, o2]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n16, eq_o16]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n17, eq_n15]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n19, eq_n18]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21, eq_n20]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_n22]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n24]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n12]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n26, eq_n27]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29]
  have eq_n31 : n31 = o31 := by
    simpa only [n31, o31, eq_n30] using
      (aux_shared1 w9 o30)
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n28]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n28]
  have eq_n35 : n35 = o13 := by
    simpa only [n35, n28, o13, eq_n27] using
      (aux_shared0 s  o27)
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n35, eq_n34, eq_o35]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36, eq_n33]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n37]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n32]
  have eq_n40 : n40 = o34 := by
    simp only [n40, o34, eq_n28]
  have eq_n41 : n41 = o13 := by
    simpa only [n41, n28, o13, eq_n27] using
      (aux_shared0 s  o27)
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41, eq_n40, eq_o41, eq_o40]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42, eq_n39]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n43]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n31, eq_n44]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n31, eq_n38]
  have eq_n47 : n47 = o47 := by
    simp only [n47, o47]
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48, eq_n47, eq_n46]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49]
  have eq_n50 : n50 = o50 := by
    simp only [n50, o50, eq_n49, eq_n48]
  have eq_n51 : n51 = o51 := by
    simp only [n51, o51]
  change {s with pc := N 7363, memory := o28, stack := o51 :: o50 :: o45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
    {s with pc := N 7363, memory := n28, stack := n51 :: n50 :: n45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}
  simp only [eq_o16, eq_o35, eq_o40, eq_o41, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51]
theorem squareColumn12_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12Program {s with pc := N 7235, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (squareColumn12Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  exact (sq12New_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact).trans
    (congrArg some (prepared_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest).symm)

#print axioms squareColumn12_run
end CycleSubmission.Execution
