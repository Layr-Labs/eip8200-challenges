import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Prepared.R5Square
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast


open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

theorem addC (a b : W) : a + b = b + a := word_add_comm a b
theorem mulC (a b : W) : a * b = b * a := by
  apply word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [mul_comm]
theorem addA (a b c : W) : (a + b) + c = a + (b + c) := by
  apply word_ext
  change ((a.val + b.val) + c.val).val = (a.val + (b.val + c.val)).val
  rw [add_assoc]
theorem addL (a b c : W) : a + (b + c) = b + (a + c) := by
  rw [← addA, addC a b, addA]
theorem mmC (a b m : W) : UInt256.mulMod a b m = UInt256.mulMod b a m := by
  simp [UInt256.mulMod, Nat.mul_comm]
theorem amC (a b m : W) : UInt256.addMod a b m = UInt256.addMod b a m := by
  simp [UInt256.addMod, Nat.add_comm]
theorem andC (a b : W) : UInt256.land a b = UInt256.land b a := by
  apply word_ext
  change (a.val &&& b.val).val = (b.val &&& a.val).val
  simp only [Fin.and_val, Nat.and_comm]
theorem orC (a b : W) : UInt256.lor a b = UInt256.lor b a := by
  apply word_ext
  change (a.val ||| b.val).val = (b.val ||| a.val).val
  simp only [Fin.or_val, Nat.or_comm]
theorem xorC (a b : W) : UInt256.xor a b = UInt256.xor b a := by
  apply word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  simp only [Fin.xor_val, Nat.xor_comm]
theorem eqC (a b : W) : UInt256.eq a b = UInt256.eq b a := by
  simp [UInt256.eq, eq_comm]
def newpart0Program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR]

def newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) : State :=
  let v0 : W := x0 * x0
  let v1 : W := x10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  {s with pc := N 4142, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest}

theorem newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart0Program {s with pc := N 4133, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 14) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart0Program, newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart1Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x1 x10
  let v1 : W := MachineState.readWord s.memory 160
  {s with pc := N 4151, memory := s.memory, stack := v1 :: x10 :: v0 :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest}

theorem newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart1Program {s with pc := N 4142, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart1Program, newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def newpart2Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x4 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod (N 2048) v1 x3
  {s with pc := N 4162, memory := s.memory, stack := x5 :: x6 :: v2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart2Program {s with pc := N 4151, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart2Program, newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart3Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD]

def newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + v0
  let v2 : W := v1 + x2
  let v3 : W := x4 * x10
  let v4 : W := v3 + v2
  {s with pc := N 4170, memory := s.memory, stack := v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart3Program {s with pc := N 4162, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart3Program, newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart4Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := x13 * x0
  let v1 : W := UInt256.shiftRight v0 (N 16)
  {s with pc := N 4179, memory := s.memory, stack := x3 :: x4 :: x12 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart4Program {s with pc := N 4170, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart4Program, newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart5Program : List Instr :=
  [.op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD]

def newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + v0
  let v2 : W := v1 + x3
  let v3 : W := UInt256.mulMod x5 x11 x15
  {s with pc := N 4187, memory := s.memory, stack := v3 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart5Program {s with pc := N 4179, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart5Program, newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := UInt256.mulMod x2 v1 x13
  let v3 : W := v2 + v0
  {s with pc := N 4196, memory := s.memory, stack := x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart6Program {s with pc := N 4187, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart6Program, newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def newpart7Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩)]

def newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x1 x0
  let v1 : W := x4 * x6
  {s with pc := N 4206, memory := s.memory, stack := v1 :: v1 :: v0 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart7Program {s with pc := N 4196, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart7Program, newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart8Program : List Instr :=
  [.op .ADD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := v0 + x2
  let v2 : W := x7 * x7
  let v3 : W := v2 + v1
  {s with pc := N 4214, memory := s.memory, stack := x5 :: x12 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart8Program {s with pc := N 4206, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart8Program, newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart9Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL]

def newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x4 * x11
  let v3 : W := v2 + v1
  let v4 : W := x16 * v3
  {s with pc := N 4222, memory := s.memory, stack := v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart9Program {s with pc := N 4214, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart9Program, newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart10Program : List Instr :=
  [.push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩)]

def newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.shiftRight x0 (N 16)
  let v1 : W := UInt256.mulMod x4 x6 x13
  {s with pc := N 4231, memory := s.memory, stack := v1 :: v1 :: x1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart10Program {s with pc := N 4222, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart10Program, newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart11Program : List Instr :=
  [.op .ADD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x7 x7 x15
  let v3 : W := v2 + v1
  {s with pc := N 4239, memory := s.memory, stack := x15 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart11Program {s with pc := N 4231, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart11Program, newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart12Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD]

def newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x4 x11 x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x3 x10 x14
  {s with pc := N 4247, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart12Program {s with pc := N 4239, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart12Program, newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart13Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 160
  let v2 : W := UInt256.mulMod x2 v1 x14
  let v3 : W := v2 + v0
  {s with pc := N 4256, memory := s.memory, stack := x14 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart13Program {s with pc := N 4247, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart13Program, newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def newpart14Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩)]

def newpart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x1 x0
  let v1 : W := x5 * x8
  {s with pc := N 4266, memory := s.memory, stack := x7 :: v1 :: v0 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart14Program {s with pc := N 4256, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart14Program, newpart14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart15Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newpart15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x8 * x0
  let v1 : W := v0 + x1
  let v2 : W := v1 + v1
  let v3 : W := v2 + x2
  {s with pc := N 4274, memory := s.memory, stack := x6 :: x14 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart15Program {s with pc := N 4266, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart15Program, newpart15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart16Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def newpart16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x5 * x13
  let v3 : W := v2 + v1
  {s with pc := N 4282, memory := s.memory, stack := x4 :: x12 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart16Program {s with pc := N 4274, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart16Program, newpart16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart17Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def newpart17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x17 * v1
  let v3 : W := UInt256.shiftRight v2 (N 16)
  {s with pc := N 4291, memory := s.memory, stack := x16 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart17Program {s with pc := N 4282, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart17Program, newpart17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart18Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart18Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x6 x9 x0
  let v1 : W := UInt256.mulMod x7 x8 x15
  let v2 : W := v1 + v0
  {s with pc := N 4299, memory := s.memory, stack := v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart18_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart18Program {s with pc := N 4291, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart18Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart18Program, newpart18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart19Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart19Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x5 x13 x15
  let v3 : W := v2 + v1
  {s with pc := N 4307, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart19_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart19Program {s with pc := N 4299, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart19Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart19Program, newpart19Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart20Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def newpart20Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x11 x14
  let v1 : W := v0 + x0
  {s with pc := N 4315, memory := s.memory, stack := x2 :: x10 :: x14 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart20_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart20Program {s with pc := N 4307, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart20Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart20Program, newpart20Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart21Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart21Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := UInt256.mulMod x4 v2 x17
  let v4 : W := v3 + v1
  {s with pc := N 4324, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart21_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart21Program {s with pc := N 4315, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart21Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart21Program, newpart21Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def newpart22Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD]

def newpart22Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x14
  let v1 : W := UInt256.mulMod x9 x5 x14
  {s with pc := N 4335, memory := s.memory, stack := v1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart22_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart22Program {s with pc := N 4324, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart22Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart22Program, newpart22Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart23Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩)]

def newpart23Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x7 x15
  let v1 : W := v0 + x0
  let v2 : W := v1 + v1
  {s with pc := N 4343, memory := s.memory, stack := x1 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart23_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart23Program {s with pc := N 4335, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart23Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart23Program, newpart23Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart24Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def newpart24Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x9 x9 x16
  let v2 : W := v1 + v0
  {s with pc := N 4351, memory := s.memory, stack := x15 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart24_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart24Program {s with pc := N 4343, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart24Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart24Program, newpart24Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart25Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart25Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x15 x17
  let v3 : W := v2 + v1
  {s with pc := N 4359, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart25_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart25Program {s with pc := N 4351, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart25Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart25Program, newpart25Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart26Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def newpart26Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x12 x15
  let v1 : W := v0 + x0
  {s with pc := N 4367, memory := s.memory, stack := x2 :: x11 :: x15 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart26_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart26Program {s with pc := N 4359, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart26Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart26Program, newpart26Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart27Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def newpart27Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := x9 * x13
  {s with pc := N 4375, memory := s.memory, stack := x10 :: x12 :: v2 :: x4 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart27_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart27Program {s with pc := N 4367, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart27Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart27Program, newpart27Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart28Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL]

def newpart28Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := v1 + v1
  let v3 : W := v2 + x3
  let v4 : W := x11 * x11
  {s with pc := N 4383, memory := s.memory, stack := v4 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart28_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart28Program {s with pc := N 4375, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart28Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart28Program, newpart28Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart29Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def newpart29Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x6 * x15
  let v2 : W := v1 + v0
  let v3 : W := x5 * x14
  {s with pc := N 4391, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart29_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart29Program {s with pc := N 4383, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart29Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart29Program, newpart29Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart30Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def newpart30Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x13
  let v2 : W := v1 + v0
  let v3 : W := x3 * x12
  {s with pc := N 4399, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart30_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart30Program {s with pc := N 4391, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart30Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart30Program, newpart30Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart31Program : List Instr :=
  [.op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP]

def newpart31Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 192
  let v2 : W := v1 * v0
  let v3 : W := UInt256.shiftRight v2 (N 16)
  {s with pc := N 4409, memory := s.memory, stack := x2 :: x3 :: x4 :: x5 :: v3 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart31_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart31Program {s with pc := N 4399, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart31Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart31Program, newpart31Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def newpart32Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩)]

def newpart32Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 160
  let v1 : W := UInt256.mulMod x4 v0 x14
  let v2 : W := v1 + x0
  {s with pc := N 4418, memory := s.memory, stack := v2 :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart32_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart32Program {s with pc := N 4409, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart32Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart32Program, newpart32Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def newpart33Program : List Instr :=
  [.push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def newpart33Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod (N 2048) x0 x1
  let v1 : W := x7 * x10
  {s with pc := N 4428, memory := s.memory, stack := x8 :: x9 :: v1 :: v0 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart33_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart33Program {s with pc := N 4418, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart33Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart33Program, newpart33Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart34Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def newpart34Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := v1 + v1
  let v3 : W := v2 + x3
  let v4 : W := x7 * x17
  {s with pc := N 4436, memory := s.memory, stack := v4 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart34_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart34Program {s with pc := N 4428, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart34Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart34Program, newpart34Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart35Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def newpart35Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x14
  let v2 : W := v1 + v0
  let v3 : W := x3 * x13
  {s with pc := N 4444, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart35_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart35Program {s with pc := N 4436, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart35Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart35Program, newpart35Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart36Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

def newpart36Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x6 * x12
  let v2 : W := v1 + v0
  {s with pc := N 4452, memory := s.memory, stack := x16 :: x16 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart36_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart36Program {s with pc := N 4444, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart36Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart36Program, newpart36Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart37Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart37Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x12 x0
  let v1 : W := UInt256.mulMod x10 x11 x1
  let v2 : W := v1 + v0
  {s with pc := N 4460, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart37_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart37Program {s with pc := N 4452, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart37Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart37Program, newpart37Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart38Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart38Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x5 x15 x16
  let v3 : W := v2 + v1
  {s with pc := N 4468, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart38_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart38Program {s with pc := N 4460, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart38Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart38Program, newpart38Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart39Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def newpart39Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x13 x15
  let v1 : W := v0 + x0
  {s with pc := N 4476, memory := s.memory, stack := x2 :: x12 :: x15 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart39_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart39Program {s with pc := N 4468, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart39Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart39Program, newpart39Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart40Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def newpart40Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x8 x14 x18
  let v3 : W := v2 + v1
  {s with pc := N 4484, memory := s.memory, stack := x4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart40_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart40Program {s with pc := N 4476, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart40Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart40Program, newpart40Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart41Program : List Instr :=
  [.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB]

def newpart41Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) x0
  let v1 : W := x1 - v0
  {s with pc := N 4522, memory := s.memory, stack := v1 :: x15 :: x2 :: x3 :: x4 :: x5 :: v0 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart41_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart41Program {s with pc := N 4484, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart41Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart41Program, newpart41Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart42Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL]

def newpart42Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x1 + x0
  let v1 : W := UInt256.mulMod (N 2048) v0 x1
  let v2 : W := x8 * x10
  {s with pc := N 4532, memory := s.memory, stack := v2 :: v1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart42_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart42Program {s with pc := N 4522, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart42Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart42Program, newpart42Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart43Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def newpart43Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x0
  let v1 : W := v0 + x1
  let v2 : W := x10 * x10
  let v3 : W := v2 + v1
  {s with pc := N 4540, memory := s.memory, stack := x15 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart43_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart43Program {s with pc := N 4532, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart43Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart43Program, newpart43Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart44Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def newpart44Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := v0 + x1
  let v2 : W := x3 * x14
  let v3 : W := v2 + v1
  {s with pc := N 4548, memory := s.memory, stack := x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart44_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart44Program {s with pc := N 4540, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart44Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart44Program, newpart44Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart45Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def newpart45Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x6 * x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x9 x11 x16
  {s with pc := N 4556, memory := s.memory, stack := v2 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart45_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart45Program {s with pc := N 4548, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart45Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart45Program, newpart45Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart46Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart46Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x10 x10 x16
  let v3 : W := v2 + v1
  {s with pc := N 4564, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart46_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart46Program {s with pc := N 4556, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart46Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart46Program, newpart46Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart47Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def newpart47Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x14 x15
  let v1 : W := v0 + x0
  {s with pc := N 4572, memory := s.memory, stack := x2 :: x13 :: x15 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart47_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart47Program {s with pc := N 4564, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart47Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart47Program, newpart47Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart48Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

def newpart48Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x8 x15 x18
  let v3 : W := v2 + v1
  {s with pc := N 4580, memory := s.memory, stack := x4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart48_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart48Program {s with pc := N 4572, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart48Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart48Program, newpart48Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart49Program : List Instr :=
  [.push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB]

def newpart49Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) x0
  let v1 : W := x1 - v0
  {s with pc := N 4618, memory := s.memory, stack := v1 :: x15 :: x2 :: x3 :: x4 :: x5 :: x6 :: v0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart49_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart49Program {s with pc := N 4580, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart49Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart49Program, newpart49Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart50Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL]

def newpart50Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x1 + x0
  let v1 : W := UInt256.mulMod (N 2048) v0 x1
  let v2 : W := x9 * x10
  {s with pc := N 4628, memory := s.memory, stack := v2 :: v1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart50_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart50Program {s with pc := N 4618, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart50Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart50Program, newpart50Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart51Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩)]

def newpart51Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x0
  let v1 : W := v0 + x1
  let v2 : W := x3 * x15
  let v3 : W := v2 + v1
  {s with pc := N 4636, memory := s.memory, stack := x14 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart51_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart51Program {s with pc := N 4628, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart51Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart51Program, newpart51Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart52Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩)]

def newpart52Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x6 * x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v1
  {s with pc := N 4674, memory := s.memory, stack := x16 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: v2 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart52_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart52Program {s with pc := N 4636, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart52Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart52Program, newpart52Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart53Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨2, by decide⟩)]

def newpart53Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x10 x9 x0
  let v1 : W := v0 + v0
  let v2 : W := v1 + x1
  {s with pc := N 4682, memory := s.memory, stack := x2 :: x15 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart53_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart53Program {s with pc := N 4674, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart53Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart53Program, newpart53Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart54Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart54Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x15 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x14 x6 x16
  let v3 : W := v2 + v1
  {s with pc := N 4690, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart54_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart54Program {s with pc := N 4682, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart54Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart54Program, newpart54Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart55Program : List Instr :=
  [.push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .SUB,
   .op .ADD,
   .op .MULMOD]

def newpart55Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 - x7
  let v1 : W := v0 + x14
  let v2 : W := UInt256.mulMod v1 (N 2048) x14
  {s with pc := N 4700, memory := s.memory, stack := v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart55_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart55Program {s with pc := N 4690, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart55Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart55Program, newpart55Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart56Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL]

def newpart56Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x9 * x9
  let v1 : W := v0 + x0
  let v2 : W := x13 * x4
  {s with pc := N 4708, memory := s.memory, stack := v2 :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart56_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart56Program {s with pc := N 4700, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart56Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart56Program, newpart56Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart57Program : List Instr :=
  [.op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

def newpart57Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v0
  {s with pc := N 4746, memory := s.memory, stack := x11 :: x11 :: x16 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: v1 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart57_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart57Program {s with pc := N 4708, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart57Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart57Program, newpart57Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart58Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048]

def newpart58Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x16 x7 x17
  let v3 : W := v2 + v1
  {s with pc := N 4756, memory := s.memory, stack := (N 2048) :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart58_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart58Program {s with pc := N 4746, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart58Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart58Program, newpart58Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart59Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .SUB,
   .op .ADD,
   .op .MULMOD,
   .op (.Swap ⟨8, by decide⟩)]

def newpart59Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x1 - x9
  let v1 : W := v0 + x15
  let v2 : W := UInt256.mulMod v1 x0 x15
  {s with pc := N 4764, memory := s.memory, stack := x10 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: v2 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart59_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = N 2048) :
    runInstructions newpart59Program {s with pc := N 4756, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart59Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hk_x0, hz, hzn, newpart59Program, newpart59Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart60Program : List Instr :=
  [.op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 1 1,
   .op (.Dup ⟨12, by decide⟩),
   .op .SUB]

def newpart60Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x16 - (N 1)
  {s with pc := N 4773, memory := s.memory, stack := v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart60_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart60Program {s with pc := N 4764, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart60Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart60Program, newpart60Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart61Program : List Instr :=
  [.op (.Swap ⟨11, by decide⟩)]

def newpart61Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W) : State :=
  {s with pc := N 4774, memory := s.memory, stack := x12 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x0 :: rest}

theorem newpart61_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart61Program {s with pc := N 4773, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest} =
      some (newpart61Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 13) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart61Program, newpart61Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 3 2048,
   .op .MULMOD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .push 1 16,
   .op .SHR,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .SUB,
   .op .ADD,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 30 1766847064778384329583297500742918515827483896875618958121606201292619775,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op .SUB,
   .op .ADD,
   .op .MULMOD,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 1 1,
   .op (.Dup ⟨12, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨11, by decide⟩)]

def newModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) : State :=
  let v0 : W := x0 * x0
  let v1 : W := x10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := UInt256.mulMod x0 x0 x9
  let v4 : W := MachineState.readWord s.memory 160
  let v5 : W := UInt256.mulMod v2 v4 x9
  let v6 : W := v5 + v3
  let v7 : W := UInt256.mulMod (N 2048) v6 x9
  let v8 : W := x0 * x1
  let v9 : W := v8 + v8
  let v10 : W := v9 + v7
  let v11 : W := v2 * x5
  let v12 : W := v11 + v10
  let v13 : W := x10 * v12
  let v14 : W := UInt256.shiftRight v13 (N 16)
  let v15 : W := UInt256.mulMod x0 x1 x9
  let v16 : W := v15 + v15
  let v17 : W := v16 + v7
  let v18 : W := UInt256.mulMod v2 x5 x9
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 160
  let v21 : W := UInt256.mulMod v14 v20 x9
  let v22 : W := v21 + v19
  let v23 : W := UInt256.mulMod (N 2048) v22 x9
  let v24 : W := x0 * x2
  let v25 : W := v24 + v24
  let v26 : W := v25 + v23
  let v27 : W := x1 * x1
  let v28 : W := v27 + v26
  let v29 : W := v2 * x6
  let v30 : W := v29 + v28
  let v31 : W := v14 * x5
  let v32 : W := v31 + v30
  let v33 : W := x10 * v32
  let v34 : W := UInt256.shiftRight v33 (N 16)
  let v35 : W := UInt256.mulMod x0 x2 x9
  let v36 : W := v35 + v35
  let v37 : W := v36 + v23
  let v38 : W := UInt256.mulMod x1 x1 x9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v2 x6 x9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v14 x5 x9
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord s.memory 160
  let v45 : W := UInt256.mulMod v34 v44 x9
  let v46 : W := v45 + v43
  let v47 : W := UInt256.mulMod (N 2048) v46 x9
  let v48 : W := x0 * x3
  let v49 : W := x1 * x2
  let v50 : W := v49 + v48
  let v51 : W := v50 + v50
  let v52 : W := v51 + v47
  let v53 : W := v2 * x7
  let v54 : W := v53 + v52
  let v55 : W := v14 * x6
  let v56 : W := v55 + v54
  let v57 : W := v34 * x5
  let v58 : W := v57 + v56
  let v59 : W := x10 * v58
  let v60 : W := UInt256.shiftRight v59 (N 16)
  let v61 : W := UInt256.mulMod x0 x3 x9
  let v62 : W := UInt256.mulMod x1 x2 x9
  let v63 : W := v62 + v61
  let v64 : W := v63 + v63
  let v65 : W := v64 + v47
  let v66 : W := UInt256.mulMod v2 x7 x9
  let v67 : W := v66 + v65
  let v68 : W := UInt256.mulMod v14 x6 x9
  let v69 : W := v68 + v67
  let v70 : W := UInt256.mulMod v34 x5 x9
  let v71 : W := v70 + v69
  let v72 : W := MachineState.readWord s.memory 160
  let v73 : W := UInt256.mulMod v60 v72 x9
  let v74 : W := v73 + v71
  let v75 : W := UInt256.mulMod (N 2048) v74 x9
  let v76 : W := UInt256.mulMod x4 x0 x9
  let v77 : W := UInt256.mulMod x3 x1 x9
  let v78 : W := v77 + v76
  let v79 : W := v78 + v78
  let v80 : W := v75 + v79
  let v81 : W := UInt256.mulMod x2 x2 x9
  let v82 : W := v81 + v80
  let v83 : W := UInt256.mulMod v2 x8 x9
  let v84 : W := v83 + v82
  let v85 : W := UInt256.mulMod v14 x7 x9
  let v86 : W := v85 + v84
  let v87 : W := UInt256.mulMod v34 x6 x9
  let v88 : W := v87 + v86
  let v89 : W := UInt256.mulMod v60 x5 x9
  let v90 : W := v89 + v88
  let v91 : W := x0 * x4
  let v92 : W := x1 * x3
  let v93 : W := v92 + v91
  let v94 : W := v93 + v93
  let v95 : W := v94 + v75
  let v96 : W := x2 * x2
  let v97 : W := v96 + v95
  let v98 : W := v2 * x8
  let v99 : W := v98 + v97
  let v100 : W := v14 * x7
  let v101 : W := v100 + v99
  let v102 : W := v34 * x6
  let v103 : W := v102 + v101
  let v104 : W := v60 * x5
  let v105 : W := v104 + v103
  let v106 : W := MachineState.readWord s.memory 192
  let v107 : W := v106 * v105
  let v108 : W := UInt256.shiftRight v107 (N 16)
  let v109 : W := MachineState.readWord s.memory 160
  let v110 : W := UInt256.mulMod v108 v109 x9
  let v111 : W := v110 + v90
  let v112 : W := UInt256.mulMod (N 2048) v111 x9
  let v113 : W := x1 * x4
  let v114 : W := x2 * x3
  let v115 : W := v114 + v113
  let v116 : W := v115 + v115
  let v117 : W := v116 + v112
  let v118 : W := v14 * x8
  let v119 : W := v118 + v117
  let v120 : W := v34 * x7
  let v121 : W := v120 + v119
  let v122 : W := v60 * x6
  let v123 : W := v122 + v121
  let v124 : W := v108 * x5
  let v125 : W := v124 + v123
  let v126 : W := UInt256.mulMod x1 x4 x9
  let v127 : W := UInt256.mulMod x2 x3 x9
  let v128 : W := v127 + v126
  let v129 : W := v128 + v128
  let v130 : W := v129 + v112
  let v131 : W := UInt256.mulMod v14 x8 x9
  let v132 : W := v131 + v130
  let v133 : W := UInt256.mulMod v34 x7 x9
  let v134 : W := v133 + v132
  let v135 : W := UInt256.mulMod v60 x6 x9
  let v136 : W := v135 + v134
  let v137 : W := UInt256.mulMod v108 x5 x9
  let v138 : W := v137 + v136
  let v139 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v125
  let v140 : W := v138 - v139
  let v141 : W := x9 + v140
  let v142 : W := UInt256.mulMod (N 2048) v141 x9
  let v143 : W := x2 * x4
  let v144 : W := v143 + v143
  let v145 : W := v144 + v142
  let v146 : W := x3 * x3
  let v147 : W := v146 + v145
  let v148 : W := v34 * x8
  let v149 : W := v148 + v147
  let v150 : W := v60 * x7
  let v151 : W := v150 + v149
  let v152 : W := v108 * x6
  let v153 : W := v152 + v151
  let v154 : W := UInt256.mulMod x2 x4 x9
  let v155 : W := v154 + v154
  let v156 : W := v155 + v142
  let v157 : W := UInt256.mulMod x3 x3 x9
  let v158 : W := v157 + v156
  let v159 : W := UInt256.mulMod v34 x8 x9
  let v160 : W := v159 + v158
  let v161 : W := UInt256.mulMod v60 x7 x9
  let v162 : W := v161 + v160
  let v163 : W := UInt256.mulMod v108 x6 x9
  let v164 : W := v163 + v162
  let v165 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v153
  let v166 : W := v164 - v165
  let v167 : W := x9 + v166
  let v168 : W := UInt256.mulMod (N 2048) v167 x9
  let v169 : W := x3 * x4
  let v170 : W := v169 + v169
  let v171 : W := v170 + v168
  let v172 : W := v60 * x8
  let v173 : W := v172 + v171
  let v174 : W := v108 * x7
  let v175 : W := v174 + v173
  let v176 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v175
  let v177 : W := UInt256.mulMod x4 x3 x9
  let v178 : W := v177 + v177
  let v179 : W := v178 + v168
  let v180 : W := UInt256.mulMod x8 v60 x9
  let v181 : W := v180 + v179
  let v182 : W := UInt256.mulMod x7 v108 x9
  let v183 : W := v182 + v181
  let v184 : W := v183 - v176
  let v185 : W := v184 + x9
  let v186 : W := UInt256.mulMod v185 (N 2048) x9
  let v187 : W := x4 * x4
  let v188 : W := v187 + v186
  let v189 : W := x8 * v108
  let v190 : W := v189 + v188
  let v191 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v190
  let v192 : W := UInt256.mulMod x4 x4 x9
  let v193 : W := v192 + v186
  let v194 : W := UInt256.mulMod x8 v108 x9
  let v195 : W := v194 + v193
  let v196 : W := v195 - v191
  let v197 : W := v196 + x9
  let v198 : W := UInt256.mulMod v197 (N 2048) x9
  let v199 : W := x11 - (N 1)
  {s with pc := N 4774, memory := s.memory, stack := x11 :: v139 :: v165 :: v176 :: v191 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v199 :: rest}

theorem new_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := N 4133, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} =
      some (newModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest) := by
  let v0 : W := x0 * x0
  let v1 : W := x10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := UInt256.mulMod x0 x0 x9
  let v4 : W := MachineState.readWord s.memory 160
  let v5 : W := UInt256.mulMod v2 v4 x9
  let v6 : W := v5 + v3
  let v7 : W := UInt256.mulMod (N 2048) v6 x9
  let v8 : W := x0 * x1
  let v9 : W := v8 + v8
  let v10 : W := v9 + v7
  let v11 : W := v2 * x5
  let v12 : W := v11 + v10
  let v13 : W := x10 * v12
  let v14 : W := UInt256.shiftRight v13 (N 16)
  let v15 : W := UInt256.mulMod x0 x1 x9
  let v16 : W := v15 + v15
  let v17 : W := v16 + v7
  let v18 : W := UInt256.mulMod v2 x5 x9
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 160
  let v21 : W := UInt256.mulMod v14 v20 x9
  let v22 : W := v21 + v19
  let v23 : W := UInt256.mulMod (N 2048) v22 x9
  let v24 : W := x0 * x2
  let v25 : W := v24 + v24
  let v26 : W := v25 + v23
  let v27 : W := x1 * x1
  let v28 : W := v27 + v26
  let v29 : W := v2 * x6
  let v30 : W := v29 + v28
  let v31 : W := v14 * x5
  let v32 : W := v31 + v30
  let v33 : W := x10 * v32
  let v34 : W := UInt256.shiftRight v33 (N 16)
  let v35 : W := UInt256.mulMod x0 x2 x9
  let v36 : W := v35 + v35
  let v37 : W := v36 + v23
  let v38 : W := UInt256.mulMod x1 x1 x9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v2 x6 x9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v14 x5 x9
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord s.memory 160
  let v45 : W := UInt256.mulMod v34 v44 x9
  let v46 : W := v45 + v43
  let v47 : W := UInt256.mulMod (N 2048) v46 x9
  let v48 : W := x0 * x3
  let v49 : W := x1 * x2
  let v50 : W := v49 + v48
  let v51 : W := v50 + v50
  let v52 : W := v51 + v47
  let v53 : W := v2 * x7
  let v54 : W := v53 + v52
  let v55 : W := v14 * x6
  let v56 : W := v55 + v54
  let v57 : W := v34 * x5
  let v58 : W := v57 + v56
  let v59 : W := x10 * v58
  let v60 : W := UInt256.shiftRight v59 (N 16)
  let v61 : W := UInt256.mulMod x0 x3 x9
  let v62 : W := UInt256.mulMod x1 x2 x9
  let v63 : W := v62 + v61
  let v64 : W := v63 + v63
  let v65 : W := v64 + v47
  let v66 : W := UInt256.mulMod v2 x7 x9
  let v67 : W := v66 + v65
  let v68 : W := UInt256.mulMod v14 x6 x9
  let v69 : W := v68 + v67
  let v70 : W := UInt256.mulMod v34 x5 x9
  let v71 : W := v70 + v69
  let v72 : W := MachineState.readWord s.memory 160
  let v73 : W := UInt256.mulMod v60 v72 x9
  let v74 : W := v73 + v71
  let v75 : W := UInt256.mulMod (N 2048) v74 x9
  let v76 : W := UInt256.mulMod x4 x0 x9
  let v77 : W := UInt256.mulMod x3 x1 x9
  let v78 : W := v77 + v76
  let v79 : W := v78 + v78
  let v80 : W := v75 + v79
  let v81 : W := UInt256.mulMod x2 x2 x9
  let v82 : W := v81 + v80
  let v83 : W := UInt256.mulMod v2 x8 x9
  let v84 : W := v83 + v82
  let v85 : W := UInt256.mulMod v14 x7 x9
  let v86 : W := v85 + v84
  let v87 : W := UInt256.mulMod v34 x6 x9
  let v88 : W := v87 + v86
  let v89 : W := UInt256.mulMod v60 x5 x9
  let v90 : W := v89 + v88
  let v91 : W := x0 * x4
  let v92 : W := x1 * x3
  let v93 : W := v92 + v91
  let v94 : W := v93 + v93
  let v95 : W := v94 + v75
  let v96 : W := x2 * x2
  let v97 : W := v96 + v95
  let v98 : W := v2 * x8
  let v99 : W := v98 + v97
  let v100 : W := v14 * x7
  let v101 : W := v100 + v99
  let v102 : W := v34 * x6
  let v103 : W := v102 + v101
  let v104 : W := v60 * x5
  let v105 : W := v104 + v103
  let v106 : W := MachineState.readWord s.memory 192
  let v107 : W := v106 * v105
  let v108 : W := UInt256.shiftRight v107 (N 16)
  let v109 : W := MachineState.readWord s.memory 160
  let v110 : W := UInt256.mulMod v108 v109 x9
  let v111 : W := v110 + v90
  let v112 : W := UInt256.mulMod (N 2048) v111 x9
  let v113 : W := x1 * x4
  let v114 : W := x2 * x3
  let v115 : W := v114 + v113
  let v116 : W := v115 + v115
  let v117 : W := v116 + v112
  let v118 : W := v14 * x8
  let v119 : W := v118 + v117
  let v120 : W := v34 * x7
  let v121 : W := v120 + v119
  let v122 : W := v60 * x6
  let v123 : W := v122 + v121
  let v124 : W := v108 * x5
  let v125 : W := v124 + v123
  let v126 : W := UInt256.mulMod x1 x4 x9
  let v127 : W := UInt256.mulMod x2 x3 x9
  let v128 : W := v127 + v126
  let v129 : W := v128 + v128
  let v130 : W := v129 + v112
  let v131 : W := UInt256.mulMod v14 x8 x9
  let v132 : W := v131 + v130
  let v133 : W := UInt256.mulMod v34 x7 x9
  let v134 : W := v133 + v132
  let v135 : W := UInt256.mulMod v60 x6 x9
  let v136 : W := v135 + v134
  let v137 : W := UInt256.mulMod v108 x5 x9
  let v138 : W := v137 + v136
  let v139 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v125
  let v140 : W := v138 - v139
  let v141 : W := x9 + v140
  let v142 : W := UInt256.mulMod (N 2048) v141 x9
  let v143 : W := x2 * x4
  let v144 : W := v143 + v143
  let v145 : W := v144 + v142
  let v146 : W := x3 * x3
  let v147 : W := v146 + v145
  let v148 : W := v34 * x8
  let v149 : W := v148 + v147
  let v150 : W := v60 * x7
  let v151 : W := v150 + v149
  let v152 : W := v108 * x6
  let v153 : W := v152 + v151
  let v154 : W := UInt256.mulMod x2 x4 x9
  let v155 : W := v154 + v154
  let v156 : W := v155 + v142
  let v157 : W := UInt256.mulMod x3 x3 x9
  let v158 : W := v157 + v156
  let v159 : W := UInt256.mulMod v34 x8 x9
  let v160 : W := v159 + v158
  let v161 : W := UInt256.mulMod v60 x7 x9
  let v162 : W := v161 + v160
  let v163 : W := UInt256.mulMod v108 x6 x9
  let v164 : W := v163 + v162
  let v165 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v153
  let v166 : W := v164 - v165
  let v167 : W := x9 + v166
  let v168 : W := UInt256.mulMod (N 2048) v167 x9
  let v169 : W := x3 * x4
  let v170 : W := v169 + v169
  let v171 : W := v170 + v168
  let v172 : W := v60 * x8
  let v173 : W := v172 + v171
  let v174 : W := v108 * x7
  let v175 : W := v174 + v173
  let v176 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v175
  let v177 : W := UInt256.mulMod x4 x3 x9
  let v178 : W := v177 + v177
  let v179 : W := v178 + v168
  let v180 : W := UInt256.mulMod x8 v60 x9
  let v181 : W := v180 + v179
  let v182 : W := UInt256.mulMod x7 v108 x9
  let v183 : W := v182 + v181
  let v184 : W := v183 - v176
  let v185 : W := v184 + x9
  let v186 : W := UInt256.mulMod v185 (N 2048) x9
  let v187 : W := x4 * x4
  let v188 : W := v187 + v186
  let v189 : W := x8 * v108
  let v190 : W := v189 + v188
  let v191 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v190
  let v192 : W := UInt256.mulMod x4 x4 x9
  let v193 : W := v192 + v186
  let v194 : W := UInt256.mulMod x8 v108 x9
  let v195 : W := v194 + v193
  let v196 : W := v195 - v191
  let v197 : W := v196 + x9
  let v198 : W := UInt256.mulMod v197 (N 2048) x9
  let v199 : W := x11 - (N 1)
  have h0 : runInstructions newpart0Program {s with pc := N 4133, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4142, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart0Model, v0, v1, v2] using newpart0_run (s) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h1 : runInstructions newpart1Program {s with pc := N 4142, memory := s.memory, stack := v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4151, memory := s.memory, stack := v4 :: x9 :: v3 :: x9 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart1Model, v3, v4] using newpart1_run (s) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h2 : runInstructions newpart2Program {s with pc := N 4151, memory := s.memory, stack := v4 :: x9 :: v3 :: x9 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4162, memory := s.memory, stack := x0 :: x1 :: v7 :: v7 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart2Model, v5, v6, v7] using newpart2_run (s) (v4) (x9) (v3) (x9) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h3 : runInstructions newpart3Program {s with pc := N 4162, memory := s.memory, stack := x0 :: x1 :: v7 :: v7 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4170, memory := s.memory, stack := v12 :: v7 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart3Model, v8, v9, v10, v11, v12] using newpart3_run (s) (x0) (x1) (v7) (v7) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h4 : runInstructions newpart4Program {s with pc := N 4170, memory := s.memory, stack := v12 :: v7 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4179, memory := s.memory, stack := x0 :: x1 :: x9 :: v7 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart4Model, v13, v14] using newpart4_run (s) (v12) (v7) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h5 : runInstructions newpart5Program {s with pc := N 4179, memory := s.memory, stack := x0 :: x1 :: x9 :: v7 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4187, memory := s.memory, stack := v18 :: v17 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart5Model, v15, v16, v17, v18] using newpart5_run (s) (x0) (x1) (x9) (v7) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h6 : runInstructions newpart6Program {s with pc := N 4187, memory := s.memory, stack := v18 :: v17 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4196, memory := s.memory, stack := x9 :: v22 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart6Model, v19, v20, v21, v22] using newpart6_run (s) (v18) (v17) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h7 : runInstructions newpart7Program {s with pc := N 4196, memory := s.memory, stack := x9 :: v22 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4206, memory := s.memory, stack := v24 :: v24 :: v23 :: v23 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart7Model, v23, v24] using newpart7_run (s) (x9) (v22) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h8 : runInstructions newpart8Program {s with pc := N 4206, memory := s.memory, stack := v24 :: v24 :: v23 :: v23 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4214, memory := s.memory, stack := v2 :: x6 :: v28 :: v23 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart8Model, v25, v26, v27, v28] using newpart8_run (s) (v24) (v24) (v23) (v23) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h9 : runInstructions newpart9Program {s with pc := N 4214, memory := s.memory, stack := v2 :: x6 :: v28 :: v23 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4222, memory := s.memory, stack := v33 :: v23 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart9Model, v29, v30, v31, v32, v33] using newpart9_run (s) (v2) (x6) (v28) (v23) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h10 : runInstructions newpart10Program {s with pc := N 4222, memory := s.memory, stack := v33 :: v23 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4231, memory := s.memory, stack := v35 :: v35 :: v23 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart10Model, v34, v35] using newpart10_run (s) (v33) (v23) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h11 : runInstructions newpart11Program {s with pc := N 4231, memory := s.memory, stack := v35 :: v35 :: v23 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4239, memory := s.memory, stack := x9 :: v39 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart11Model, v36, v37, v38, v39] using newpart11_run (s) (v35) (v35) (v23) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h12 : runInstructions newpart12Program {s with pc := N 4239, memory := s.memory, stack := x9 :: v39 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4247, memory := s.memory, stack := v42 :: v41 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart12Model, v40, v41, v42] using newpart12_run (s) (x9) (v39) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h13 : runInstructions newpart13Program {s with pc := N 4247, memory := s.memory, stack := v42 :: v41 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4256, memory := s.memory, stack := x9 :: v46 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart13Model, v43, v44, v45, v46] using newpart13_run (s) (v42) (v41) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h14 : runInstructions newpart14Program {s with pc := N 4256, memory := s.memory, stack := x9 :: v46 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4266, memory := s.memory, stack := x2 :: v48 :: v47 :: v47 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart14Model, v47, v48] using newpart14_run (s) (x9) (v46) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h15 : runInstructions newpart15Program {s with pc := N 4266, memory := s.memory, stack := x2 :: v48 :: v47 :: v47 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4274, memory := s.memory, stack := v2 :: x7 :: v52 :: v47 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart15Model, v49, v50, v51, v52] using newpart15_run (s) (x2) (v48) (v47) (v47) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h16 : runInstructions newpart16Program {s with pc := N 4274, memory := s.memory, stack := v2 :: x7 :: v52 :: v47 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4282, memory := s.memory, stack := v34 :: x5 :: v56 :: v47 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart16Model, v53, v54, v55, v56] using newpart16_run (s) (v2) (x7) (v52) (v47) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h17 : runInstructions newpart17Program {s with pc := N 4282, memory := s.memory, stack := v34 :: x5 :: v56 :: v47 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4291, memory := s.memory, stack := x9 :: v47 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart17Model, v57, v58, v59, v60] using newpart17_run (s) (v34) (x5) (v56) (v47) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h18 : runInstructions newpart18Program {s with pc := N 4291, memory := s.memory, stack := x9 :: v47 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4299, memory := s.memory, stack := v63 :: v47 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart18Model, v61, v62, v63] using newpart18_run (s) (x9) (v47) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h19 : runInstructions newpart19Program {s with pc := N 4299, memory := s.memory, stack := v63 :: v47 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4307, memory := s.memory, stack := v67 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart19Model, v64, v65, v66, v67] using newpart19_run (s) (v63) (v47) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h20 : runInstructions newpart20Program {s with pc := N 4307, memory := s.memory, stack := v67 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4315, memory := s.memory, stack := v34 :: x5 :: x9 :: v69 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart20Model, v68, v69] using newpart20_run (s) (v67) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h21 : runInstructions newpart21Program {s with pc := N 4315, memory := s.memory, stack := v34 :: x5 :: x9 :: v69 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4324, memory := s.memory, stack := v74 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart21Model, v70, v71, v72, v73, v74] using newpart21_run (s) (v34) (x5) (x9) (v69) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h22 : runInstructions newpart22Program {s with pc := N 4324, memory := s.memory, stack := v74 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4335, memory := s.memory, stack := v76 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart22Model, v75, v76] using newpart22_run (s) (v74) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h23 : runInstructions newpart23Program {s with pc := N 4335, memory := s.memory, stack := v76 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4343, memory := s.memory, stack := v75 :: v79 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart23Model, v77, v78, v79] using newpart23_run (s) (v76) (v75) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h24 : runInstructions newpart24Program {s with pc := N 4343, memory := s.memory, stack := v75 :: v79 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4351, memory := s.memory, stack := x8 :: x9 :: v82 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart24Model, v80, v81, v82] using newpart24_run (s) (v75) (v79) (v75) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h25 : runInstructions newpart25Program {s with pc := N 4351, memory := s.memory, stack := x8 :: x9 :: v82 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4359, memory := s.memory, stack := v86 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart25Model, v83, v84, v85, v86] using newpart25_run (s) (x8) (x9) (v82) (v75) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h26 : runInstructions newpart26Program {s with pc := N 4359, memory := s.memory, stack := v86 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4367, memory := s.memory, stack := v60 :: x5 :: x9 :: v88 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart26Model, v87, v88] using newpart26_run (s) (v86) (v75) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h27 : runInstructions newpart27Program {s with pc := N 4367, memory := s.memory, stack := v60 :: x5 :: x9 :: v88 :: v75 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4375, memory := s.memory, stack := x1 :: x3 :: v91 :: v75 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart27Model, v89, v90, v91] using newpart27_run (s) (v60) (x5) (x9) (v88) (v75) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h28 : runInstructions newpart28Program {s with pc := N 4375, memory := s.memory, stack := x1 :: x3 :: v91 :: v75 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4383, memory := s.memory, stack := v96 :: v95 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart28Model, v92, v93, v94, v95, v96] using newpart28_run (s) (x1) (x3) (v91) (v75) (v90) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h29 : runInstructions newpart29Program {s with pc := N 4383, memory := s.memory, stack := v96 :: v95 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4391, memory := s.memory, stack := v100 :: v99 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart29Model, v97, v98, v99, v100] using newpart29_run (s) (v96) (v95) (v90) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h30 : runInstructions newpart30Program {s with pc := N 4391, memory := s.memory, stack := v100 :: v99 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4399, memory := s.memory, stack := v104 :: v103 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart30Model, v101, v102, v103, v104] using newpart30_run (s) (v100) (v99) (v90) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h31 : runInstructions newpart31Program {s with pc := N 4399, memory := s.memory, stack := v104 :: v103 :: v90 :: v60 :: v34 :: v14 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4409, memory := s.memory, stack := v90 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart31Model, v105, v106, v107, v108] using newpart31_run (s) (v104) (v103) (v90) (v60) (v34) (v14) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h32 : runInstructions newpart32Program {s with pc := N 4409, memory := s.memory, stack := v90 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4418, memory := s.memory, stack := v111 :: x9 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart32Model, v109, v110, v111] using newpart32_run (s) (v90) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h33 : runInstructions newpart33Program {s with pc := N 4418, memory := s.memory, stack := v111 :: x9 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4428, memory := s.memory, stack := x2 :: x3 :: v113 :: v112 :: v112 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart33Model, v112, v113] using newpart33_run (s) (v111) (x9) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h34 : runInstructions newpart34Program {s with pc := N 4428, memory := s.memory, stack := x2 :: x3 :: v113 :: v112 :: v112 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4436, memory := s.memory, stack := v118 :: v117 :: v112 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart34Model, v114, v115, v116, v117, v118] using newpart34_run (s) (x2) (x3) (v113) (v112) (v112) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h35 : runInstructions newpart35Program {s with pc := N 4436, memory := s.memory, stack := v118 :: v117 :: v112 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4444, memory := s.memory, stack := v122 :: v121 :: v112 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart35Model, v119, v120, v121, v122] using newpart35_run (s) (v118) (v117) (v112) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h36 : runInstructions newpart36Program {s with pc := N 4444, memory := s.memory, stack := v122 :: v121 :: v112 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4452, memory := s.memory, stack := x9 :: x9 :: v112 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart36Model, v123, v124, v125] using newpart36_run (s) (v122) (v121) (v112) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h37 : runInstructions newpart37Program {s with pc := N 4452, memory := s.memory, stack := x9 :: x9 :: v112 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4460, memory := s.memory, stack := v128 :: v112 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart37Model, v126, v127, v128] using newpart37_run (s) (x9) (x9) (v112) (v125) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h38 : runInstructions newpart38Program {s with pc := N 4460, memory := s.memory, stack := v128 :: v112 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4468, memory := s.memory, stack := v132 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart38Model, v129, v130, v131, v132] using newpart38_run (s) (v128) (v112) (v125) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h39 : runInstructions newpart39Program {s with pc := N 4468, memory := s.memory, stack := v132 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4476, memory := s.memory, stack := v60 :: x6 :: x9 :: v134 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart39Model, v133, v134] using newpart39_run (s) (v132) (v125) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h40 : runInstructions newpart40Program {s with pc := N 4476, memory := s.memory, stack := v60 :: x6 :: x9 :: v134 :: v125 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4484, memory := s.memory, stack := v125 :: v138 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart40Model, v135, v136, v137, v138] using newpart40_run (s) (v60) (x6) (x9) (v134) (v125) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h41 : runInstructions newpart41Program {s with pc := N 4484, memory := s.memory, stack := v125 :: v138 :: v60 :: v34 :: v14 :: v108 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4522, memory := s.memory, stack := v140 :: x9 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart41Model, v139, v140] using newpart41_run (s) (v125) (v138) (v60) (v34) (v14) (v108) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h42 : runInstructions newpart42Program {s with pc := N 4522, memory := s.memory, stack := v140 :: x9 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4532, memory := s.memory, stack := v143 :: v142 :: v142 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart42Model, v141, v142, v143] using newpart42_run (s) (v140) (x9) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h43 : runInstructions newpart43Program {s with pc := N 4532, memory := s.memory, stack := v143 :: v142 :: v142 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4540, memory := s.memory, stack := x8 :: v147 :: v142 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart43Model, v144, v145, v146, v147] using newpart43_run (s) (v143) (v142) (v142) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h44 : runInstructions newpart44Program {s with pc := N 4540, memory := s.memory, stack := x8 :: v147 :: v142 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4548, memory := s.memory, stack := x6 :: v151 :: v142 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart44Model, v148, v149, v150, v151] using newpart44_run (s) (x8) (v147) (v142) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h45 : runInstructions newpart45Program {s with pc := N 4548, memory := s.memory, stack := x6 :: v151 :: v142 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4556, memory := s.memory, stack := v154 :: v142 :: v153 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart45Model, v152, v153, v154] using newpart45_run (s) (x6) (v151) (v142) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h46 : runInstructions newpart46Program {s with pc := N 4556, memory := s.memory, stack := v154 :: v142 :: v153 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4564, memory := s.memory, stack := v158 :: v153 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart46Model, v155, v156, v157, v158] using newpart46_run (s) (v154) (v142) (v153) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h47 : runInstructions newpart47Program {s with pc := N 4564, memory := s.memory, stack := v158 :: v153 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4572, memory := s.memory, stack := v60 :: x7 :: x9 :: v160 :: v153 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart47Model, v159, v160] using newpart47_run (s) (v158) (v153) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h48 : runInstructions newpart48Program {s with pc := N 4572, memory := s.memory, stack := v60 :: x7 :: x9 :: v160 :: v153 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4580, memory := s.memory, stack := v153 :: v164 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart48Model, v161, v162, v163, v164] using newpart48_run (s) (v60) (x7) (x9) (v160) (v153) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h49 : runInstructions newpart49Program {s with pc := N 4580, memory := s.memory, stack := v153 :: v164 :: v60 :: v34 :: v14 :: v108 :: v139 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4618, memory := s.memory, stack := v166 :: x9 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart49Model, v165, v166] using newpart49_run (s) (v153) (v164) (v60) (v34) (v14) (v108) (v139) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h50 : runInstructions newpart50Program {s with pc := N 4618, memory := s.memory, stack := v166 :: x9 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4628, memory := s.memory, stack := v169 :: v168 :: v168 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart50Model, v167, v168, v169] using newpart50_run (s) (v166) (x9) (v60) (v34) (v14) (v108) (v139) (v165) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h51 : runInstructions newpart51Program {s with pc := N 4628, memory := s.memory, stack := v169 :: v168 :: v168 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4636, memory := s.memory, stack := x7 :: v173 :: v168 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart51Model, v170, v171, v172, v173] using newpart51_run (s) (v169) (v168) (v168) (v60) (v34) (v14) (v108) (v139) (v165) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h52 : runInstructions newpart52Program {s with pc := N 4636, memory := s.memory, stack := x7 :: v173 :: v168 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4674, memory := s.memory, stack := x9 :: v168 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart52Model, v174, v175, v176] using newpart52_run (s) (x7) (v173) (v168) (v60) (v34) (v14) (v108) (v139) (v165) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h53 : runInstructions newpart53Program {s with pc := N 4674, memory := s.memory, stack := x9 :: v168 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4682, memory := s.memory, stack := v60 :: x9 :: v179 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart53Model, v177, v178, v179] using newpart53_run (s) (x9) (v168) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h54 : runInstructions newpart54Program {s with pc := N 4682, memory := s.memory, stack := v60 :: x9 :: v179 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4690, memory := s.memory, stack := v183 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart54Model, v180, v181, v182, v183] using newpart54_run (s) (v60) (x9) (v179) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h55 : runInstructions newpart55Program {s with pc := N 4690, memory := s.memory, stack := v183 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4700, memory := s.memory, stack := v186 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart55Model, v184, v185, v186] using newpart55_run (s) (v183) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h56 : runInstructions newpart56Program {s with pc := N 4700, memory := s.memory, stack := v186 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4708, memory := s.memory, stack := v189 :: v188 :: v186 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart56Model, v187, v188, v189] using newpart56_run (s) (v186) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h57 : runInstructions newpart57Program {s with pc := N 4708, memory := s.memory, stack := v189 :: v188 :: v186 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4746, memory := s.memory, stack := x4 :: x4 :: x9 :: v186 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: v191 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart57Model, v190, v191] using newpart57_run (s) (v189) (v188) (v186) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h58 : runInstructions newpart58Program {s with pc := N 4746, memory := s.memory, stack := x4 :: x4 :: x9 :: v186 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: v191 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4756, memory := s.memory, stack := (N 2048) :: v195 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: v191 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart58Model, v192, v193, v194, v195] using newpart58_run (s) (x4) (x4) (x9) (v186) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (v191) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h59 : runInstructions newpart59Program {s with pc := N 4756, memory := s.memory, stack := (N 2048) :: v195 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: v191 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4764, memory := s.memory, stack := x4 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: v191 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart59Model, v196, v197, v198] using newpart59_run (s) ((N 2048)) (v195) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (v191) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact (by rfl)
  have h60 : runInstructions newpart60Program {s with pc := N 4764, memory := s.memory, stack := x4 :: v60 :: v34 :: v14 :: v108 :: v139 :: v165 :: v176 :: v191 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4773, memory := s.memory, stack := v199 :: v139 :: v165 :: v176 :: v191 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} := by
    simpa only [newpart60Model, v199] using newpart60_run (s) (x4) (v60) (v34) (v14) (v108) (v139) (v165) (v176) (v191) (v198) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  have h61 : runInstructions newpart61Program {s with pc := N 4773, memory := s.memory, stack := v199 :: v139 :: v165 :: v176 :: v191 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: rest} = some {s with pc := N 4774, memory := s.memory, stack := x11 :: v139 :: v165 :: v176 :: v191 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v199 :: rest} := by
    simpa only [newpart61Model] using newpart61_run (s) (v199) (v139) (v165) (v176) (v191) (v198) (x5) (x6) (x7) (x8) (x9) (x10) (x11) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 (runInstructions_append_some _ _ _ _ _ h21 (runInstructions_append_some _ _ _ _ _ h22 (runInstructions_append_some _ _ _ _ _ h23 (runInstructions_append_some _ _ _ _ _ h24 (runInstructions_append_some _ _ _ _ _ h25 (runInstructions_append_some _ _ _ _ _ h26 (runInstructions_append_some _ _ _ _ _ h27 (runInstructions_append_some _ _ _ _ _ h28 (runInstructions_append_some _ _ _ _ _ h29 (runInstructions_append_some _ _ _ _ _ h30 (runInstructions_append_some _ _ _ _ _ h31 (runInstructions_append_some _ _ _ _ _ h32 (runInstructions_append_some _ _ _ _ _ h33 (runInstructions_append_some _ _ _ _ _ h34 (runInstructions_append_some _ _ _ _ _ h35 (runInstructions_append_some _ _ _ _ _ h36 (runInstructions_append_some _ _ _ _ _ h37 (runInstructions_append_some _ _ _ _ _ h38 (runInstructions_append_some _ _ _ _ _ h39 (runInstructions_append_some _ _ _ _ _ h40 (runInstructions_append_some _ _ _ _ _ h41 (runInstructions_append_some _ _ _ _ _ h42 (runInstructions_append_some _ _ _ _ _ h43 (runInstructions_append_some _ _ _ _ _ h44 (runInstructions_append_some _ _ _ _ _ h45 (runInstructions_append_some _ _ _ _ _ h46 (runInstructions_append_some _ _ _ _ _ h47 (runInstructions_append_some _ _ _ _ _ h48 (runInstructions_append_some _ _ _ _ _ h49 (runInstructions_append_some _ _ _ _ _ h50 (runInstructions_append_some _ _ _ _ _ h51 (runInstructions_append_some _ _ _ _ _ h52 (runInstructions_append_some _ _ _ _ _ h53 (runInstructions_append_some _ _ _ _ _ h54 (runInstructions_append_some _ _ _ _ _ h55 (runInstructions_append_some _ _ _ _ _ h56 (runInstructions_append_some _ _ _ _ _ h57 (runInstructions_append_some _ _ _ _ _ h58 (runInstructions_append_some _ _ _ _ _ h59 (runInstructions_append_some _ _ _ _ _ h60 h61)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

#print axioms new_run

def oldModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) : State :=
  let v0 : W := x0 * x0
  let v1 : W := x10 * v0
  let v2 : W := UInt256.shiftRight v1 (N 16)
  let v3 : W := UInt256.mulMod x0 x0 x9
  let v4 : W := MachineState.readWord s.memory 160
  let v5 : W := UInt256.mulMod v2 v4 x9
  let v6 : W := v5 + v3
  let v7 : W := UInt256.mulMod (N 2048) v6 x9
  let v8 : W := x0 * x1
  let v9 : W := v8 + v8
  let v10 : W := v9 + v7
  let v11 : W := v2 * x5
  let v12 : W := v11 + v10
  let v13 : W := x10 * v12
  let v14 : W := UInt256.shiftRight v13 (N 16)
  let v15 : W := UInt256.mulMod x0 x1 x9
  let v16 : W := v15 + v15
  let v17 : W := v16 + v7
  let v18 : W := UInt256.mulMod v2 x5 x9
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 160
  let v21 : W := UInt256.mulMod v14 v20 x9
  let v22 : W := v21 + v19
  let v23 : W := UInt256.mulMod (N 2048) v22 x9
  let v24 : W := x0 * x2
  let v25 : W := v24 + v24
  let v26 : W := v25 + v23
  let v27 : W := x1 * x1
  let v28 : W := v27 + v26
  let v29 : W := v2 * x6
  let v30 : W := v29 + v28
  let v31 : W := v14 * x5
  let v32 : W := v31 + v30
  let v33 : W := x10 * v32
  let v34 : W := UInt256.shiftRight v33 (N 16)
  let v35 : W := UInt256.mulMod x0 x2 x9
  let v36 : W := v35 + v35
  let v37 : W := v36 + v23
  let v38 : W := UInt256.mulMod x1 x1 x9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod v2 x6 x9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.mulMod v14 x5 x9
  let v43 : W := v42 + v41
  let v44 : W := MachineState.readWord s.memory 160
  let v45 : W := UInt256.mulMod v34 v44 x9
  let v46 : W := v45 + v43
  let v47 : W := UInt256.mulMod (N 2048) v46 x9
  let v48 : W := x0 * x3
  let v49 : W := x1 * x2
  let v50 : W := v49 + v48
  let v51 : W := v50 + v50
  let v52 : W := v51 + v47
  let v53 : W := v2 * x7
  let v54 : W := v53 + v52
  let v55 : W := v14 * x6
  let v56 : W := v55 + v54
  let v57 : W := v34 * x5
  let v58 : W := v57 + v56
  let v59 : W := x10 * v58
  let v60 : W := UInt256.shiftRight v59 (N 16)
  let v61 : W := UInt256.mulMod x0 x3 x9
  let v62 : W := UInt256.mulMod x1 x2 x9
  let v63 : W := v62 + v61
  let v64 : W := v63 + v63
  let v65 : W := v64 + v47
  let v66 : W := UInt256.mulMod v2 x7 x9
  let v67 : W := v66 + v65
  let v68 : W := UInt256.mulMod v14 x6 x9
  let v69 : W := v68 + v67
  let v70 : W := UInt256.mulMod v34 x5 x9
  let v71 : W := v70 + v69
  let v72 : W := MachineState.readWord s.memory 160
  let v73 : W := UInt256.mulMod v60 v72 x9
  let v74 : W := v73 + v71
  let v75 : W := UInt256.mulMod (N 2048) v74 x9
  let v76 : W := UInt256.mulMod x0 x4 x9
  let v77 : W := UInt256.mulMod x1 x3 x9
  let v78 : W := v77 + v76
  let v79 : W := v78 + v78
  let v80 : W := v79 + v75
  let v81 : W := UInt256.mulMod x2 x2 x9
  let v82 : W := v81 + v80
  let v83 : W := UInt256.mulMod v2 x8 x9
  let v84 : W := v83 + v82
  let v85 : W := UInt256.mulMod v14 x7 x9
  let v86 : W := v85 + v84
  let v87 : W := UInt256.mulMod v34 x6 x9
  let v88 : W := v87 + v86
  let v89 : W := UInt256.mulMod v60 x5 x9
  let v90 : W := v89 + v88
  let v91 : W := x0 * x4
  let v92 : W := x1 * x3
  let v93 : W := v92 + v91
  let v94 : W := v93 + v93
  let v95 : W := v94 + v75
  let v96 : W := x2 * x2
  let v97 : W := v96 + v95
  let v98 : W := v2 * x8
  let v99 : W := v98 + v97
  let v100 : W := v14 * x7
  let v101 : W := v100 + v99
  let v102 : W := v34 * x6
  let v103 : W := v102 + v101
  let v104 : W := v60 * x5
  let v105 : W := v104 + v103
  let v106 : W := MachineState.readWord s.memory 192
  let v107 : W := v106 * v105
  let v108 : W := UInt256.shiftRight v107 (N 16)
  let v109 : W := MachineState.readWord s.memory 160
  let v110 : W := UInt256.mulMod v108 v109 x9
  let v111 : W := v110 + v90
  let v112 : W := UInt256.mulMod (N 2048) v111 x9
  let v113 : W := x1 * x4
  let v114 : W := x2 * x3
  let v115 : W := v114 + v113
  let v116 : W := v115 + v115
  let v117 : W := v116 + v112
  let v118 : W := v14 * x8
  let v119 : W := v118 + v117
  let v120 : W := v34 * x7
  let v121 : W := v120 + v119
  let v122 : W := v60 * x6
  let v123 : W := v122 + v121
  let v124 : W := v108 * x5
  let v125 : W := v124 + v123
  let v126 : W := UInt256.mulMod x1 x4 x9
  let v127 : W := UInt256.mulMod x2 x3 x9
  let v128 : W := v127 + v126
  let v129 : W := v128 + v128
  let v130 : W := v129 + v112
  let v131 : W := UInt256.mulMod v14 x8 x9
  let v132 : W := v131 + v130
  let v133 : W := UInt256.mulMod v34 x7 x9
  let v134 : W := v133 + v132
  let v135 : W := UInt256.mulMod v60 x6 x9
  let v136 : W := v135 + v134
  let v137 : W := UInt256.mulMod v108 x5 x9
  let v138 : W := v137 + v136
  let v139 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v125
  let v140 : W := v138 - v139
  let v141 : W := x9 + v140
  let v142 : W := UInt256.mulMod v141 (N 2048) x9
  let v143 : W := x2 * x4
  let v144 : W := v143 + v143
  let v145 : W := v144 + v142
  let v146 : W := x3 * x3
  let v147 : W := v146 + v145
  let v148 : W := v34 * x8
  let v149 : W := v148 + v147
  let v150 : W := v60 * x7
  let v151 : W := v150 + v149
  let v152 : W := v108 * x6
  let v153 : W := v152 + v151
  let v154 : W := UInt256.mulMod x2 x4 x9
  let v155 : W := v154 + v154
  let v156 : W := v155 + v142
  let v157 : W := UInt256.mulMod x3 x3 x9
  let v158 : W := v157 + v156
  let v159 : W := UInt256.mulMod v34 x8 x9
  let v160 : W := v159 + v158
  let v161 : W := UInt256.mulMod v60 x7 x9
  let v162 : W := v161 + v160
  let v163 : W := UInt256.mulMod v108 x6 x9
  let v164 : W := v163 + v162
  let v165 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v153
  let v166 : W := v164 - v165
  let v167 : W := x9 + v166
  let v168 : W := UInt256.mulMod v167 (N 2048) x9
  let v169 : W := x3 * x4
  let v170 : W := v169 + v169
  let v171 : W := v170 + v168
  let v172 : W := v60 * x8
  let v173 : W := v172 + v171
  let v174 : W := v108 * x7
  let v175 : W := v174 + v173
  let v176 : W := UInt256.mulMod x3 x4 x9
  let v177 : W := v176 + v176
  let v178 : W := v177 + v168
  let v179 : W := UInt256.mulMod v60 x8 x9
  let v180 : W := v179 + v178
  let v181 : W := UInt256.mulMod v108 x7 x9
  let v182 : W := v181 + v180
  let v183 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v175
  let v184 : W := v182 - v183
  let v185 : W := x9 + v184
  let v186 : W := UInt256.mulMod v185 (N 2048) x9
  let v187 : W := x4 * x4
  let v188 : W := v187 + v186
  let v189 : W := v108 * x8
  let v190 : W := v189 + v188
  let v191 : W := UInt256.mulMod x4 x4 x9
  let v192 : W := v191 + v186
  let v193 : W := UInt256.mulMod v108 x8 x9
  let v194 : W := v193 + v192
  let v195 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) v190
  let v196 : W := v194 - v195
  let v197 : W := x9 + v196
  let v198 : W := UInt256.mulMod v197 (N 2048) x9
  let v199 : W := x11 - (N 1)
  {s with pc := N 4774, memory := s.memory, stack := x11 :: v139 :: v165 :: v183 :: v195 :: v198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v199 :: rest}

private theorem aux_shared0 (x0 x4 x9 : W) :
    (UInt256.mulMod x4 x0 x9) = (UInt256.mulMod x0 x4 x9) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared1 (x1 x3 x9 : W) :
    (UInt256.mulMod x3 x1 x9) = (UInt256.mulMod x1 x3 x9) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared2 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared3 (x9 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 x9) = (UInt256.mulMod z0 (N 2048) x9) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared4 (x3 x4 x9 : W) :
    (UInt256.mulMod x4 x3 x9) = (UInt256.mulMod x3 x4 x9) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared5 (x8 x9 : W) (z0 : W) :
    (UInt256.mulMod x8 z0 x9) = (UInt256.mulMod z0 x8 x9) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared6 (x7 x9 : W) (z0 : W) :
    (UInt256.mulMod x7 z0 x9) = (UInt256.mulMod z0 x7 x9) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared7 (x9 : W) (z0 : W) :
    (z0 + x9) = (x9 + z0) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared8 (x8 : W) (z0 : W) :
    (x8 * z0) = (z0 * x8) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

theorem same_state (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : W) (rest : List W) :
    oldModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest = newModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 rest := by
  let o0 : W := x0 * x0
  let o1 : W := x10 * o0
  let o2 : W := UInt256.shiftRight o1 (N 16)
  let o3 : W := UInt256.mulMod x0 x0 x9
  let o4 : W := MachineState.readWord s.memory 160
  let o5 : W := UInt256.mulMod o2 o4 x9
  let o6 : W := o5 + o3
  let o7 : W := UInt256.mulMod (N 2048) o6 x9
  let o8 : W := x0 * x1
  let o9 : W := o8 + o8
  let o10 : W := o9 + o7
  let o11 : W := o2 * x5
  let o12 : W := o11 + o10
  let o13 : W := x10 * o12
  let o14 : W := UInt256.shiftRight o13 (N 16)
  let o15 : W := UInt256.mulMod x0 x1 x9
  let o16 : W := o15 + o15
  let o17 : W := o16 + o7
  let o18 : W := UInt256.mulMod o2 x5 x9
  let o19 : W := o18 + o17
  let o20 : W := MachineState.readWord s.memory 160
  let o21 : W := UInt256.mulMod o14 o20 x9
  let o22 : W := o21 + o19
  let o23 : W := UInt256.mulMod (N 2048) o22 x9
  let o24 : W := x0 * x2
  let o25 : W := o24 + o24
  let o26 : W := o25 + o23
  let o27 : W := x1 * x1
  let o28 : W := o27 + o26
  let o29 : W := o2 * x6
  let o30 : W := o29 + o28
  let o31 : W := o14 * x5
  let o32 : W := o31 + o30
  let o33 : W := x10 * o32
  let o34 : W := UInt256.shiftRight o33 (N 16)
  let o35 : W := UInt256.mulMod x0 x2 x9
  let o36 : W := o35 + o35
  let o37 : W := o36 + o23
  let o38 : W := UInt256.mulMod x1 x1 x9
  let o39 : W := o38 + o37
  let o40 : W := UInt256.mulMod o2 x6 x9
  let o41 : W := o40 + o39
  let o42 : W := UInt256.mulMod o14 x5 x9
  let o43 : W := o42 + o41
  let o44 : W := MachineState.readWord s.memory 160
  let o45 : W := UInt256.mulMod o34 o44 x9
  let o46 : W := o45 + o43
  let o47 : W := UInt256.mulMod (N 2048) o46 x9
  let o48 : W := x0 * x3
  let o49 : W := x1 * x2
  let o50 : W := o49 + o48
  let o51 : W := o50 + o50
  let o52 : W := o51 + o47
  let o53 : W := o2 * x7
  let o54 : W := o53 + o52
  let o55 : W := o14 * x6
  let o56 : W := o55 + o54
  let o57 : W := o34 * x5
  let o58 : W := o57 + o56
  let o59 : W := x10 * o58
  let o60 : W := UInt256.shiftRight o59 (N 16)
  let o61 : W := UInt256.mulMod x0 x3 x9
  let o62 : W := UInt256.mulMod x1 x2 x9
  let o63 : W := o62 + o61
  let o64 : W := o63 + o63
  let o65 : W := o64 + o47
  let o66 : W := UInt256.mulMod o2 x7 x9
  let o67 : W := o66 + o65
  let o68 : W := UInt256.mulMod o14 x6 x9
  let o69 : W := o68 + o67
  let o70 : W := UInt256.mulMod o34 x5 x9
  let o71 : W := o70 + o69
  let o72 : W := MachineState.readWord s.memory 160
  let o73 : W := UInt256.mulMod o60 o72 x9
  let o74 : W := o73 + o71
  let o75 : W := UInt256.mulMod (N 2048) o74 x9
  let o76 : W := UInt256.mulMod x0 x4 x9
  let o77 : W := UInt256.mulMod x1 x3 x9
  let o78 : W := o77 + o76
  let o79 : W := o78 + o78
  let o80 : W := o79 + o75
  let o81 : W := UInt256.mulMod x2 x2 x9
  let o82 : W := o81 + o80
  let o83 : W := UInt256.mulMod o2 x8 x9
  let o84 : W := o83 + o82
  let o85 : W := UInt256.mulMod o14 x7 x9
  let o86 : W := o85 + o84
  let o87 : W := UInt256.mulMod o34 x6 x9
  let o88 : W := o87 + o86
  let o89 : W := UInt256.mulMod o60 x5 x9
  let o90 : W := o89 + o88
  let o91 : W := x0 * x4
  let o92 : W := x1 * x3
  let o93 : W := o92 + o91
  let o94 : W := o93 + o93
  let o95 : W := o94 + o75
  let o96 : W := x2 * x2
  let o97 : W := o96 + o95
  let o98 : W := o2 * x8
  let o99 : W := o98 + o97
  let o100 : W := o14 * x7
  let o101 : W := o100 + o99
  let o102 : W := o34 * x6
  let o103 : W := o102 + o101
  let o104 : W := o60 * x5
  let o105 : W := o104 + o103
  let o106 : W := MachineState.readWord s.memory 192
  let o107 : W := o106 * o105
  let o108 : W := UInt256.shiftRight o107 (N 16)
  let o109 : W := MachineState.readWord s.memory 160
  let o110 : W := UInt256.mulMod o108 o109 x9
  let o111 : W := o110 + o90
  let o112 : W := UInt256.mulMod (N 2048) o111 x9
  let o113 : W := x1 * x4
  let o114 : W := x2 * x3
  let o115 : W := o114 + o113
  let o116 : W := o115 + o115
  let o117 : W := o116 + o112
  let o118 : W := o14 * x8
  let o119 : W := o118 + o117
  let o120 : W := o34 * x7
  let o121 : W := o120 + o119
  let o122 : W := o60 * x6
  let o123 : W := o122 + o121
  let o124 : W := o108 * x5
  let o125 : W := o124 + o123
  let o126 : W := UInt256.mulMod x1 x4 x9
  let o127 : W := UInt256.mulMod x2 x3 x9
  let o128 : W := o127 + o126
  let o129 : W := o128 + o128
  let o130 : W := o129 + o112
  let o131 : W := UInt256.mulMod o14 x8 x9
  let o132 : W := o131 + o130
  let o133 : W := UInt256.mulMod o34 x7 x9
  let o134 : W := o133 + o132
  let o135 : W := UInt256.mulMod o60 x6 x9
  let o136 : W := o135 + o134
  let o137 : W := UInt256.mulMod o108 x5 x9
  let o138 : W := o137 + o136
  let o139 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) o125
  let o140 : W := o138 - o139
  let o141 : W := x9 + o140
  let o142 : W := UInt256.mulMod o141 (N 2048) x9
  let o143 : W := x2 * x4
  let o144 : W := o143 + o143
  let o145 : W := o144 + o142
  let o146 : W := x3 * x3
  let o147 : W := o146 + o145
  let o148 : W := o34 * x8
  let o149 : W := o148 + o147
  let o150 : W := o60 * x7
  let o151 : W := o150 + o149
  let o152 : W := o108 * x6
  let o153 : W := o152 + o151
  let o154 : W := UInt256.mulMod x2 x4 x9
  let o155 : W := o154 + o154
  let o156 : W := o155 + o142
  let o157 : W := UInt256.mulMod x3 x3 x9
  let o158 : W := o157 + o156
  let o159 : W := UInt256.mulMod o34 x8 x9
  let o160 : W := o159 + o158
  let o161 : W := UInt256.mulMod o60 x7 x9
  let o162 : W := o161 + o160
  let o163 : W := UInt256.mulMod o108 x6 x9
  let o164 : W := o163 + o162
  let o165 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) o153
  let o166 : W := o164 - o165
  let o167 : W := x9 + o166
  let o168 : W := UInt256.mulMod o167 (N 2048) x9
  let o169 : W := x3 * x4
  let o170 : W := o169 + o169
  let o171 : W := o170 + o168
  let o172 : W := o60 * x8
  let o173 : W := o172 + o171
  let o174 : W := o108 * x7
  let o175 : W := o174 + o173
  let o176 : W := UInt256.mulMod x3 x4 x9
  let o177 : W := o176 + o176
  let o178 : W := o177 + o168
  let o179 : W := UInt256.mulMod o60 x8 x9
  let o180 : W := o179 + o178
  let o181 : W := UInt256.mulMod o108 x7 x9
  let o182 : W := o181 + o180
  let o183 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) o175
  let o184 : W := o182 - o183
  let o185 : W := x9 + o184
  let o186 : W := UInt256.mulMod o185 (N 2048) x9
  let o187 : W := x4 * x4
  let o188 : W := o187 + o186
  let o189 : W := o108 * x8
  let o190 : W := o189 + o188
  let o191 : W := UInt256.mulMod x4 x4 x9
  let o192 : W := o191 + o186
  let o193 : W := UInt256.mulMod o108 x8 x9
  let o194 : W := o193 + o192
  let o195 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) o190
  let o196 : W := o194 - o195
  let o197 : W := x9 + o196
  let o198 : W := UInt256.mulMod o197 (N 2048) x9
  let o199 : W := x11 - (N 1)
  let n0 : W := x0 * x0
  let n1 : W := x10 * n0
  let n2 : W := UInt256.shiftRight n1 (N 16)
  let n3 : W := UInt256.mulMod x0 x0 x9
  let n4 : W := MachineState.readWord s.memory 160
  let n5 : W := UInt256.mulMod n2 n4 x9
  let n6 : W := n5 + n3
  let n7 : W := UInt256.mulMod (N 2048) n6 x9
  let n8 : W := x0 * x1
  let n9 : W := n8 + n8
  let n10 : W := n9 + n7
  let n11 : W := n2 * x5
  let n12 : W := n11 + n10
  let n13 : W := x10 * n12
  let n14 : W := UInt256.shiftRight n13 (N 16)
  let n15 : W := UInt256.mulMod x0 x1 x9
  let n16 : W := n15 + n15
  let n17 : W := n16 + n7
  let n18 : W := UInt256.mulMod n2 x5 x9
  let n19 : W := n18 + n17
  let n20 : W := MachineState.readWord s.memory 160
  let n21 : W := UInt256.mulMod n14 n20 x9
  let n22 : W := n21 + n19
  let n23 : W := UInt256.mulMod (N 2048) n22 x9
  let n24 : W := x0 * x2
  let n25 : W := n24 + n24
  let n26 : W := n25 + n23
  let n27 : W := x1 * x1
  let n28 : W := n27 + n26
  let n29 : W := n2 * x6
  let n30 : W := n29 + n28
  let n31 : W := n14 * x5
  let n32 : W := n31 + n30
  let n33 : W := x10 * n32
  let n34 : W := UInt256.shiftRight n33 (N 16)
  let n35 : W := UInt256.mulMod x0 x2 x9
  let n36 : W := n35 + n35
  let n37 : W := n36 + n23
  let n38 : W := UInt256.mulMod x1 x1 x9
  let n39 : W := n38 + n37
  let n40 : W := UInt256.mulMod n2 x6 x9
  let n41 : W := n40 + n39
  let n42 : W := UInt256.mulMod n14 x5 x9
  let n43 : W := n42 + n41
  let n44 : W := MachineState.readWord s.memory 160
  let n45 : W := UInt256.mulMod n34 n44 x9
  let n46 : W := n45 + n43
  let n47 : W := UInt256.mulMod (N 2048) n46 x9
  let n48 : W := x0 * x3
  let n49 : W := x1 * x2
  let n50 : W := n49 + n48
  let n51 : W := n50 + n50
  let n52 : W := n51 + n47
  let n53 : W := n2 * x7
  let n54 : W := n53 + n52
  let n55 : W := n14 * x6
  let n56 : W := n55 + n54
  let n57 : W := n34 * x5
  let n58 : W := n57 + n56
  let n59 : W := x10 * n58
  let n60 : W := UInt256.shiftRight n59 (N 16)
  let n61 : W := UInt256.mulMod x0 x3 x9
  let n62 : W := UInt256.mulMod x1 x2 x9
  let n63 : W := n62 + n61
  let n64 : W := n63 + n63
  let n65 : W := n64 + n47
  let n66 : W := UInt256.mulMod n2 x7 x9
  let n67 : W := n66 + n65
  let n68 : W := UInt256.mulMod n14 x6 x9
  let n69 : W := n68 + n67
  let n70 : W := UInt256.mulMod n34 x5 x9
  let n71 : W := n70 + n69
  let n72 : W := MachineState.readWord s.memory 160
  let n73 : W := UInt256.mulMod n60 n72 x9
  let n74 : W := n73 + n71
  let n75 : W := UInt256.mulMod (N 2048) n74 x9
  let n76 : W := UInt256.mulMod x4 x0 x9
  let n77 : W := UInt256.mulMod x3 x1 x9
  let n78 : W := n77 + n76
  let n79 : W := n78 + n78
  let n80 : W := n75 + n79
  let n81 : W := UInt256.mulMod x2 x2 x9
  let n82 : W := n81 + n80
  let n83 : W := UInt256.mulMod n2 x8 x9
  let n84 : W := n83 + n82
  let n85 : W := UInt256.mulMod n14 x7 x9
  let n86 : W := n85 + n84
  let n87 : W := UInt256.mulMod n34 x6 x9
  let n88 : W := n87 + n86
  let n89 : W := UInt256.mulMod n60 x5 x9
  let n90 : W := n89 + n88
  let n91 : W := x0 * x4
  let n92 : W := x1 * x3
  let n93 : W := n92 + n91
  let n94 : W := n93 + n93
  let n95 : W := n94 + n75
  let n96 : W := x2 * x2
  let n97 : W := n96 + n95
  let n98 : W := n2 * x8
  let n99 : W := n98 + n97
  let n100 : W := n14 * x7
  let n101 : W := n100 + n99
  let n102 : W := n34 * x6
  let n103 : W := n102 + n101
  let n104 : W := n60 * x5
  let n105 : W := n104 + n103
  let n106 : W := MachineState.readWord s.memory 192
  let n107 : W := n106 * n105
  let n108 : W := UInt256.shiftRight n107 (N 16)
  let n109 : W := MachineState.readWord s.memory 160
  let n110 : W := UInt256.mulMod n108 n109 x9
  let n111 : W := n110 + n90
  let n112 : W := UInt256.mulMod (N 2048) n111 x9
  let n113 : W := x1 * x4
  let n114 : W := x2 * x3
  let n115 : W := n114 + n113
  let n116 : W := n115 + n115
  let n117 : W := n116 + n112
  let n118 : W := n14 * x8
  let n119 : W := n118 + n117
  let n120 : W := n34 * x7
  let n121 : W := n120 + n119
  let n122 : W := n60 * x6
  let n123 : W := n122 + n121
  let n124 : W := n108 * x5
  let n125 : W := n124 + n123
  let n126 : W := UInt256.mulMod x1 x4 x9
  let n127 : W := UInt256.mulMod x2 x3 x9
  let n128 : W := n127 + n126
  let n129 : W := n128 + n128
  let n130 : W := n129 + n112
  let n131 : W := UInt256.mulMod n14 x8 x9
  let n132 : W := n131 + n130
  let n133 : W := UInt256.mulMod n34 x7 x9
  let n134 : W := n133 + n132
  let n135 : W := UInt256.mulMod n60 x6 x9
  let n136 : W := n135 + n134
  let n137 : W := UInt256.mulMod n108 x5 x9
  let n138 : W := n137 + n136
  let n139 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) n125
  let n140 : W := n138 - n139
  let n141 : W := x9 + n140
  let n142 : W := UInt256.mulMod (N 2048) n141 x9
  let n143 : W := x2 * x4
  let n144 : W := n143 + n143
  let n145 : W := n144 + n142
  let n146 : W := x3 * x3
  let n147 : W := n146 + n145
  let n148 : W := n34 * x8
  let n149 : W := n148 + n147
  let n150 : W := n60 * x7
  let n151 : W := n150 + n149
  let n152 : W := n108 * x6
  let n153 : W := n152 + n151
  let n154 : W := UInt256.mulMod x2 x4 x9
  let n155 : W := n154 + n154
  let n156 : W := n155 + n142
  let n157 : W := UInt256.mulMod x3 x3 x9
  let n158 : W := n157 + n156
  let n159 : W := UInt256.mulMod n34 x8 x9
  let n160 : W := n159 + n158
  let n161 : W := UInt256.mulMod n60 x7 x9
  let n162 : W := n161 + n160
  let n163 : W := UInt256.mulMod n108 x6 x9
  let n164 : W := n163 + n162
  let n165 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) n153
  let n166 : W := n164 - n165
  let n167 : W := x9 + n166
  let n168 : W := UInt256.mulMod (N 2048) n167 x9
  let n169 : W := x3 * x4
  let n170 : W := n169 + n169
  let n171 : W := n170 + n168
  let n172 : W := n60 * x8
  let n173 : W := n172 + n171
  let n174 : W := n108 * x7
  let n175 : W := n174 + n173
  let n176 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) n175
  let n177 : W := UInt256.mulMod x4 x3 x9
  let n178 : W := n177 + n177
  let n179 : W := n178 + n168
  let n180 : W := UInt256.mulMod x8 n60 x9
  let n181 : W := n180 + n179
  let n182 : W := UInt256.mulMod x7 n108 x9
  let n183 : W := n182 + n181
  let n184 : W := n183 - n176
  let n185 : W := n184 + x9
  let n186 : W := UInt256.mulMod n185 (N 2048) x9
  let n187 : W := x4 * x4
  let n188 : W := n187 + n186
  let n189 : W := x8 * n108
  let n190 : W := n189 + n188
  let n191 : W := UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) n190
  let n192 : W := UInt256.mulMod x4 x4 x9
  let n193 : W := n192 + n186
  let n194 : W := UInt256.mulMod x8 n108 x9
  let n195 : W := n194 + n193
  let n196 : W := n195 - n191
  let n197 : W := n196 + x9
  let n198 : W := UInt256.mulMod n197 (N 2048) x9
  let n199 : W := x11 - (N 1)
  have eq_o20 : o20 = o4 := by
    simp only [o20, o4]
  have eq_o44 : o44 = o4 := by
    simp only [o44, o4]
  have eq_o72 : o72 = o4 := by
    simp only [o72, o4]
  have eq_o109 : o109 = o4 := by
    simp only [o109, o4]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n2, eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5, eq_n3]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9, eq_n7]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n2]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n10]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n12]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n13]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16, eq_n15]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n16, eq_n7]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n2]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18, eq_n17]
  have eq_n20 : n20 = o4 := by
    simp only [n20, o4]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n14, eq_n20, eq_o20]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21, eq_n19]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23, eq_n22]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n23]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27, eq_n26]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n2]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29, eq_n28]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n14]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n31, eq_n30]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n35]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36, eq_n23]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38, eq_n37]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n2]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n40, eq_n39]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n14]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42, eq_n41]
  have eq_n44 : n44 = o4 := by
    simp only [n44, o4]
  have eq_n45 : n45 = o45 := by
    simp only [n45, o45, eq_n34, eq_n44, eq_o44]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n45, eq_n43]
  have eq_n47 : n47 = o47 := by
    simp only [n47, o47, eq_n46]
  have eq_n48 : n48 = o48 := by
    simp only [n48, o48]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49]
  have eq_n50 : n50 = o50 := by
    simp only [n50, o50, eq_n49, eq_n48]
  have eq_n51 : n51 = o51 := by
    simp only [n51, o51, eq_n50]
  have eq_n52 : n52 = o52 := by
    simp only [n52, o52, eq_n51, eq_n47]
  have eq_n53 : n53 = o53 := by
    simp only [n53, o53, eq_n2]
  have eq_n54 : n54 = o54 := by
    simp only [n54, o54, eq_n53, eq_n52]
  have eq_n55 : n55 = o55 := by
    simp only [n55, o55, eq_n14]
  have eq_n56 : n56 = o56 := by
    simp only [n56, o56, eq_n55, eq_n54]
  have eq_n57 : n57 = o57 := by
    simp only [n57, o57, eq_n34]
  have eq_n58 : n58 = o58 := by
    simp only [n58, o58, eq_n57, eq_n56]
  have eq_n59 : n59 = o59 := by
    simp only [n59, o59, eq_n58]
  have eq_n60 : n60 = o60 := by
    simp only [n60, o60, eq_n59]
  have eq_n61 : n61 = o61 := by
    simp only [n61, o61]
  have eq_n62 : n62 = o62 := by
    simp only [n62, o62]
  have eq_n63 : n63 = o63 := by
    simp only [n63, o63, eq_n62, eq_n61]
  have eq_n64 : n64 = o64 := by
    simp only [n64, o64, eq_n63]
  have eq_n65 : n65 = o65 := by
    simp only [n65, o65, eq_n64, eq_n47]
  have eq_n66 : n66 = o66 := by
    simp only [n66, o66, eq_n2]
  have eq_n67 : n67 = o67 := by
    simp only [n67, o67, eq_n66, eq_n65]
  have eq_n68 : n68 = o68 := by
    simp only [n68, o68, eq_n14]
  have eq_n69 : n69 = o69 := by
    simp only [n69, o69, eq_n68, eq_n67]
  have eq_n70 : n70 = o70 := by
    simp only [n70, o70, eq_n34]
  have eq_n71 : n71 = o71 := by
    simp only [n71, o71, eq_n70, eq_n69]
  have eq_n72 : n72 = o4 := by
    simp only [n72, o4]
  have eq_n73 : n73 = o73 := by
    simp only [n73, o73, eq_n60, eq_n72, eq_o72]
  have eq_n74 : n74 = o74 := by
    simp only [n74, o74, eq_n73, eq_n71]
  have eq_n75 : n75 = o75 := by
    simp only [n75, o75, eq_n74]
  have eq_n76 : n76 = o76 := by
    simpa only [n76, o76] using
      (aux_shared0 x0 x4 x9 )
  have eq_n77 : n77 = o77 := by
    simpa only [n77, o77] using
      (aux_shared1 x1 x3 x9 )
  have eq_n78 : n78 = o78 := by
    simp only [n78, o78, eq_n77, eq_n76]
  have eq_n79 : n79 = o79 := by
    simp only [n79, o79, eq_n78]
  have eq_n80 : n80 = o80 := by
    simpa only [n80, o80, eq_n75, eq_n79] using
      (aux_shared2  o75 o79)
  have eq_n81 : n81 = o81 := by
    simp only [n81, o81]
  have eq_n82 : n82 = o82 := by
    simp only [n82, o82, eq_n81, eq_n80]
  have eq_n83 : n83 = o83 := by
    simp only [n83, o83, eq_n2]
  have eq_n84 : n84 = o84 := by
    simp only [n84, o84, eq_n83, eq_n82]
  have eq_n85 : n85 = o85 := by
    simp only [n85, o85, eq_n14]
  have eq_n86 : n86 = o86 := by
    simp only [n86, o86, eq_n85, eq_n84]
  have eq_n87 : n87 = o87 := by
    simp only [n87, o87, eq_n34]
  have eq_n88 : n88 = o88 := by
    simp only [n88, o88, eq_n87, eq_n86]
  have eq_n89 : n89 = o89 := by
    simp only [n89, o89, eq_n60]
  have eq_n90 : n90 = o90 := by
    simp only [n90, o90, eq_n89, eq_n88]
  have eq_n91 : n91 = o91 := by
    simp only [n91, o91]
  have eq_n92 : n92 = o92 := by
    simp only [n92, o92]
  have eq_n93 : n93 = o93 := by
    simp only [n93, o93, eq_n92, eq_n91]
  have eq_n94 : n94 = o94 := by
    simp only [n94, o94, eq_n93]
  have eq_n95 : n95 = o95 := by
    simp only [n95, o95, eq_n94, eq_n75]
  have eq_n96 : n96 = o96 := by
    simp only [n96, o96]
  have eq_n97 : n97 = o97 := by
    simp only [n97, o97, eq_n96, eq_n95]
  have eq_n98 : n98 = o98 := by
    simp only [n98, o98, eq_n2]
  have eq_n99 : n99 = o99 := by
    simp only [n99, o99, eq_n98, eq_n97]
  have eq_n100 : n100 = o100 := by
    simp only [n100, o100, eq_n14]
  have eq_n101 : n101 = o101 := by
    simp only [n101, o101, eq_n100, eq_n99]
  have eq_n102 : n102 = o102 := by
    simp only [n102, o102, eq_n34]
  have eq_n103 : n103 = o103 := by
    simp only [n103, o103, eq_n102, eq_n101]
  have eq_n104 : n104 = o104 := by
    simp only [n104, o104, eq_n60]
  have eq_n105 : n105 = o105 := by
    simp only [n105, o105, eq_n104, eq_n103]
  have eq_n106 : n106 = o106 := by
    simp only [n106, o106]
  have eq_n107 : n107 = o107 := by
    simp only [n107, o107, eq_n106, eq_n105]
  have eq_n108 : n108 = o108 := by
    simp only [n108, o108, eq_n107]
  have eq_n109 : n109 = o4 := by
    simp only [n109, o4]
  have eq_n110 : n110 = o110 := by
    simp only [n110, o110, eq_n108, eq_n109, eq_o109]
  have eq_n111 : n111 = o111 := by
    simp only [n111, o111, eq_n110, eq_n90]
  have eq_n112 : n112 = o112 := by
    simp only [n112, o112, eq_n111]
  have eq_n113 : n113 = o113 := by
    simp only [n113, o113]
  have eq_n114 : n114 = o114 := by
    simp only [n114, o114]
  have eq_n115 : n115 = o115 := by
    simp only [n115, o115, eq_n114, eq_n113]
  have eq_n116 : n116 = o116 := by
    simp only [n116, o116, eq_n115]
  have eq_n117 : n117 = o117 := by
    simp only [n117, o117, eq_n116, eq_n112]
  have eq_n118 : n118 = o118 := by
    simp only [n118, o118, eq_n14]
  have eq_n119 : n119 = o119 := by
    simp only [n119, o119, eq_n118, eq_n117]
  have eq_n120 : n120 = o120 := by
    simp only [n120, o120, eq_n34]
  have eq_n121 : n121 = o121 := by
    simp only [n121, o121, eq_n120, eq_n119]
  have eq_n122 : n122 = o122 := by
    simp only [n122, o122, eq_n60]
  have eq_n123 : n123 = o123 := by
    simp only [n123, o123, eq_n122, eq_n121]
  have eq_n124 : n124 = o124 := by
    simp only [n124, o124, eq_n108]
  have eq_n125 : n125 = o125 := by
    simp only [n125, o125, eq_n124, eq_n123]
  have eq_n126 : n126 = o126 := by
    simp only [n126, o126]
  have eq_n127 : n127 = o127 := by
    simp only [n127, o127]
  have eq_n128 : n128 = o128 := by
    simp only [n128, o128, eq_n127, eq_n126]
  have eq_n129 : n129 = o129 := by
    simp only [n129, o129, eq_n128]
  have eq_n130 : n130 = o130 := by
    simp only [n130, o130, eq_n129, eq_n112]
  have eq_n131 : n131 = o131 := by
    simp only [n131, o131, eq_n14]
  have eq_n132 : n132 = o132 := by
    simp only [n132, o132, eq_n131, eq_n130]
  have eq_n133 : n133 = o133 := by
    simp only [n133, o133, eq_n34]
  have eq_n134 : n134 = o134 := by
    simp only [n134, o134, eq_n133, eq_n132]
  have eq_n135 : n135 = o135 := by
    simp only [n135, o135, eq_n60]
  have eq_n136 : n136 = o136 := by
    simp only [n136, o136, eq_n135, eq_n134]
  have eq_n137 : n137 = o137 := by
    simp only [n137, o137, eq_n108]
  have eq_n138 : n138 = o138 := by
    simp only [n138, o138, eq_n137, eq_n136]
  have eq_n139 : n139 = o139 := by
    simp only [n139, o139, eq_n125]
  have eq_n140 : n140 = o140 := by
    simp only [n140, o140, eq_n138, eq_n139]
  have eq_n141 : n141 = o141 := by
    simp only [n141, o141, eq_n140]
  have eq_n142 : n142 = o142 := by
    simpa only [n142, o142, eq_n141] using
      (aux_shared3 x9 o141)
  have eq_n143 : n143 = o143 := by
    simp only [n143, o143]
  have eq_n144 : n144 = o144 := by
    simp only [n144, o144, eq_n143]
  have eq_n145 : n145 = o145 := by
    simp only [n145, o145, eq_n144, eq_n142]
  have eq_n146 : n146 = o146 := by
    simp only [n146, o146]
  have eq_n147 : n147 = o147 := by
    simp only [n147, o147, eq_n146, eq_n145]
  have eq_n148 : n148 = o148 := by
    simp only [n148, o148, eq_n34]
  have eq_n149 : n149 = o149 := by
    simp only [n149, o149, eq_n148, eq_n147]
  have eq_n150 : n150 = o150 := by
    simp only [n150, o150, eq_n60]
  have eq_n151 : n151 = o151 := by
    simp only [n151, o151, eq_n150, eq_n149]
  have eq_n152 : n152 = o152 := by
    simp only [n152, o152, eq_n108]
  have eq_n153 : n153 = o153 := by
    simp only [n153, o153, eq_n152, eq_n151]
  have eq_n154 : n154 = o154 := by
    simp only [n154, o154]
  have eq_n155 : n155 = o155 := by
    simp only [n155, o155, eq_n154]
  have eq_n156 : n156 = o156 := by
    simp only [n156, o156, eq_n155, eq_n142]
  have eq_n157 : n157 = o157 := by
    simp only [n157, o157]
  have eq_n158 : n158 = o158 := by
    simp only [n158, o158, eq_n157, eq_n156]
  have eq_n159 : n159 = o159 := by
    simp only [n159, o159, eq_n34]
  have eq_n160 : n160 = o160 := by
    simp only [n160, o160, eq_n159, eq_n158]
  have eq_n161 : n161 = o161 := by
    simp only [n161, o161, eq_n60]
  have eq_n162 : n162 = o162 := by
    simp only [n162, o162, eq_n161, eq_n160]
  have eq_n163 : n163 = o163 := by
    simp only [n163, o163, eq_n108]
  have eq_n164 : n164 = o164 := by
    simp only [n164, o164, eq_n163, eq_n162]
  have eq_n165 : n165 = o165 := by
    simp only [n165, o165, eq_n153]
  have eq_n166 : n166 = o166 := by
    simp only [n166, o166, eq_n164, eq_n165]
  have eq_n167 : n167 = o167 := by
    simp only [n167, o167, eq_n166]
  have eq_n168 : n168 = o168 := by
    simpa only [n168, o168, eq_n167] using
      (aux_shared3 x9 o167)
  have eq_n169 : n169 = o169 := by
    simp only [n169, o169]
  have eq_n170 : n170 = o170 := by
    simp only [n170, o170, eq_n169]
  have eq_n171 : n171 = o171 := by
    simp only [n171, o171, eq_n170, eq_n168]
  have eq_n172 : n172 = o172 := by
    simp only [n172, o172, eq_n60]
  have eq_n173 : n173 = o173 := by
    simp only [n173, o173, eq_n172, eq_n171]
  have eq_n174 : n174 = o174 := by
    simp only [n174, o174, eq_n108]
  have eq_n175 : n175 = o175 := by
    simp only [n175, o175, eq_n174, eq_n173]
  have eq_n176 : n176 = o183 := by
    simp only [n176, o183, eq_n175]
  have eq_n177 : n177 = o176 := by
    simpa only [n177, o176] using
      (aux_shared4 x3 x4 x9 )
  have eq_n178 : n178 = o177 := by
    simp only [n178, o177, eq_n177]
  have eq_n179 : n179 = o178 := by
    simp only [n179, o178, eq_n178, eq_n168]
  have eq_n180 : n180 = o179 := by
    simpa only [n180, o179, eq_n60] using
      (aux_shared5 x8 x9 o60)
  have eq_n181 : n181 = o180 := by
    simp only [n181, o180, eq_n180, eq_n179]
  have eq_n182 : n182 = o181 := by
    simpa only [n182, o181, eq_n108] using
      (aux_shared6 x7 x9 o108)
  have eq_n183 : n183 = o182 := by
    simp only [n183, o182, eq_n182, eq_n181]
  have eq_n184 : n184 = o184 := by
    simp only [n184, o184, eq_n183, eq_n176]
  have eq_n185 : n185 = o185 := by
    simpa only [n185, o185, eq_n184] using
      (aux_shared7 x9 o184)
  have eq_n186 : n186 = o186 := by
    simp only [n186, o186, eq_n185]
  have eq_n187 : n187 = o187 := by
    simp only [n187, o187]
  have eq_n188 : n188 = o188 := by
    simp only [n188, o188, eq_n187, eq_n186]
  have eq_n189 : n189 = o189 := by
    simpa only [n189, o189, eq_n108] using
      (aux_shared8 x8 o108)
  have eq_n190 : n190 = o190 := by
    simp only [n190, o190, eq_n189, eq_n188]
  have eq_n191 : n191 = o195 := by
    simp only [n191, o195, eq_n190]
  have eq_n192 : n192 = o191 := by
    simp only [n192, o191]
  have eq_n193 : n193 = o192 := by
    simp only [n193, o192, eq_n192, eq_n186]
  have eq_n194 : n194 = o193 := by
    simpa only [n194, o193, eq_n108] using
      (aux_shared5 x8 x9 o108)
  have eq_n195 : n195 = o194 := by
    simp only [n195, o194, eq_n194, eq_n193]
  have eq_n196 : n196 = o196 := by
    simp only [n196, o196, eq_n195, eq_n191]
  have eq_n197 : n197 = o197 := by
    simpa only [n197, o197, eq_n196] using
      (aux_shared7 x9 o196)
  have eq_n198 : n198 = o198 := by
    simp only [n198, o198, eq_n197]
  have eq_n199 : n199 = o199 := by
    simp only [n199, o199]
  change {s with pc := N 4774, memory := s.memory, stack := x11 :: o139 :: o165 :: o183 :: o195 :: o198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: o199 :: rest} =
    {s with pc := N 4774, memory := s.memory, stack := x11 :: n139 :: n165 :: n176 :: n191 :: n198 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: n199 :: rest}
  simp only [eq_o20, eq_o44, eq_o72, eq_o109, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51, eq_n52, eq_n53, eq_n54, eq_n55, eq_n56, eq_n57, eq_n58, eq_n59, eq_n60, eq_n61, eq_n62, eq_n63, eq_n64, eq_n65, eq_n66, eq_n67, eq_n68, eq_n69, eq_n70, eq_n71, eq_n72, eq_n73, eq_n74, eq_n75, eq_n76, eq_n77, eq_n78, eq_n79, eq_n80, eq_n81, eq_n82, eq_n83, eq_n84, eq_n85, eq_n86, eq_n87, eq_n88, eq_n89, eq_n90, eq_n91, eq_n92, eq_n93, eq_n94, eq_n95, eq_n96, eq_n97, eq_n98, eq_n99, eq_n100, eq_n101, eq_n102, eq_n103, eq_n104, eq_n105, eq_n106, eq_n107, eq_n108, eq_n109, eq_n110, eq_n111, eq_n112, eq_n113, eq_n114, eq_n115, eq_n116, eq_n117, eq_n118, eq_n119, eq_n120, eq_n121, eq_n122, eq_n123, eq_n124, eq_n125, eq_n126, eq_n127, eq_n128, eq_n129, eq_n130, eq_n131, eq_n132, eq_n133, eq_n134, eq_n135, eq_n136, eq_n137, eq_n138, eq_n139, eq_n140, eq_n141, eq_n142, eq_n143, eq_n144, eq_n145, eq_n146, eq_n147, eq_n148, eq_n149, eq_n150, eq_n151, eq_n152, eq_n153, eq_n154, eq_n155, eq_n156, eq_n157, eq_n158, eq_n159, eq_n160, eq_n161, eq_n162, eq_n163, eq_n164, eq_n165, eq_n166, eq_n167, eq_n168, eq_n169, eq_n170, eq_n171, eq_n172, eq_n173, eq_n174, eq_n175, eq_n176, eq_n177, eq_n178, eq_n179, eq_n180, eq_n181, eq_n182, eq_n183, eq_n184, eq_n185, eq_n186, eq_n187, eq_n188, eq_n189, eq_n190, eq_n191, eq_n192, eq_n193, eq_n194, eq_n195, eq_n196, eq_n197, eq_n198, eq_n199]

#print axioms same_state
end CycleSubmission.Prepared.R5Square
