import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Prepared.R5Product
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
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD]

def newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := x6 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 96
  {s with pc := N 4885, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart0Program {s with pc := N 4874, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart0Program, newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha128, hf128]


def newpart1Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD]

def newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x9 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 64
  let v3 : W := x10 * v2
  let v4 : W := v3 + v1
  {s with pc := N 4894, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart1Program {s with pc := N 4885, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart1Program, newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def newpart2Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := x10 * v0
  let v2 : W := v1 + x0
  let v3 : W := x4 * x14
  {s with pc := N 4903, memory := s.memory, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart2Program {s with pc := N 4894, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart2Program, newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]


def newpart3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x14
  let v2 : W := v1 + v0
  let v3 : W := x3 * x13
  {s with pc := N 4911, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart3Program {s with pc := N 4903, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart3Program, newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x6 * x12
  let v2 : W := v1 + v0
  let v3 : W := MachineState.readWord s.memory 128
  {s with pc := N 4921, memory := s.memory, stack := v3 :: x16 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart4Program {s with pc := N 4911, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart4Program, newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def newpart5Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := UInt256.mulMod x10 v2 x17
  {s with pc := N 4930, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart5Program {s with pc := N 4921, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart5Program, newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def newpart6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 64
  let v2 : W := UInt256.mulMod x10 v1 x16
  let v3 : W := v2 + v0
  {s with pc := N 4939, memory := s.memory, stack := x16 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart6Program {s with pc := N 4930, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart6Program, newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def newpart7Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]

def newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 32
  let v1 : W := UInt256.mulMod x11 v0 x0
  let v2 : W := v1 + x1
  {s with pc := N 4948, memory := s.memory, stack := x5 :: x15 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart7Program {s with pc := N 4939, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart7Program, newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]


def newpart8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩)]

def newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x6 x16 x18
  let v3 : W := v2 + v1
  {s with pc := N 4956, memory := s.memory, stack := x18 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart8Program {s with pc := N 4948, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart8Program, newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart9Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x13 x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x6 x12 x16
  {s with pc := N 4964, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart9Program {s with pc := N 4956, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart9Program, newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart10Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .push 2 224,
   .op .MLOAD,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩)]

def newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := UInt256.land v1 x2
  {s with pc := N 4974, memory := s.memory, stack := v0 :: v2 :: x3 :: x4 :: x5 :: x6 :: v2 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart10Program {s with pc := N 4964, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart10Program, newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart11Program : List Instr :=
  [.op .SUB,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩)]

def newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x0 - x1
  let v1 : W := x15 + v0
  let v2 : W := UInt256.mulMod v1 (N 2048) x15
  {s with pc := N 4984, memory := s.memory, stack := v2 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart11Program {s with pc := N 4974, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart11Program, newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart12Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := x8 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 96
  {s with pc := N 4994, memory := s.memory, stack := x9 :: v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart12Program {s with pc := N 4984, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart12Program, newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha128, hf128]


def newpart13Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩)]

def newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 64
  let v3 : W := x12 * v2
  let v4 : W := v3 + v1
  {s with pc := N 5003, memory := s.memory, stack := x16 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart13Program {s with pc := N 4994, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart13Program, newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def newpart14Program : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩)]

def newpart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := v0 + x1
  let v2 : W := x3 * x14
  let v3 : W := v2 + v1
  {s with pc := N 5011, memory := s.memory, stack := x13 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart14Program {s with pc := N 5003, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart14Program, newpart14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart15Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def newpart15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x6 * x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 128
  {s with pc := N 5020, memory := s.memory, stack := x9 :: v2 :: x16 :: x2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart15Program {s with pc := N 5011, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart15Program, newpart15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def newpart16Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := UInt256.mulMod x12 v2 x18
  let v4 : W := v3 + v1
  {s with pc := N 5029, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart16Program {s with pc := N 5020, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart16Program, newpart16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def newpart17Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def newpart17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := UInt256.mulMod x10 v0 x15
  let v2 : W := v1 + x0
  {s with pc := N 5038, memory := s.memory, stack := x14 :: x15 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart17Program {s with pc := N 5029, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart17Program, newpart17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def newpart18Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart18Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x4 x15 x17
  let v3 : W := v2 + v1
  {s with pc := N 5046, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart18_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart18Program {s with pc := N 5038, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart18Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart18Program, newpart18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart19Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .push 2 224,
   .op .MLOAD]

def newpart19Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x12 x15
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 224
  {s with pc := N 5057, memory := s.memory, stack := v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: v1 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart19_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart19Program {s with pc := N 5046, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart19Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart19Program, newpart19Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart20Program : List Instr :=
  [.op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩)]

def newpart20Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x0 x1
  let v1 : W := x7 - v0
  let v2 : W := x15 + v1
  {s with pc := N 5067, memory := s.memory, stack := x15 :: (N 2048) :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: v0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart20_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart20Program {s with pc := N 5057, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart20Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart20Program, newpart20Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart21Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD]

def newpart21Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x2 x1 x0
  let v1 : W := MachineState.readWord s.memory 128
  let v2 : W := x10 * v1
  let v3 : W := v2 + v0
  {s with pc := N 5076, memory := s.memory, stack := v3 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart21_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) (hk_x1 : x1 = N 2048) :
    runInstructions newpart21Program {s with pc := N 5067, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart21Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hk_x1, hz, hzn, newpart21Program, newpart21Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def newpart22Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def newpart22Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 96
  let v1 : W := x10 * v0
  let v2 : W := v1 + x0
  let v3 : W := x2 * x14
  {s with pc := N 5085, memory := s.memory, stack := v3 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart22_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart22Program {s with pc := N 5076, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart22Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart22Program, newpart22Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def newpart23Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def newpart23Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x6 * x14
  let v2 : W := v1 + v0
  let v3 : W := MachineState.readWord s.memory 128
  {s with pc := N 5095, memory := s.memory, stack := v3 :: x16 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart23_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart23Program {s with pc := N 5085, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart23Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart23Program, newpart23Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def newpart24Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD]

def newpart24Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x11 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := UInt256.mulMod x12 v2 x17
  {s with pc := N 5104, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart24_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart24Program {s with pc := N 5095, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart24Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart24Program, newpart24Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96]


def newpart25Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def newpart25Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x3 x15 x16
  let v2 : W := v1 + v0
  {s with pc := N 5112, memory := s.memory, stack := x14 :: x16 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart25_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart25Program {s with pc := N 5104, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart25Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart25Program, newpart25Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart26Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push 2 224,
   .op .MLOAD,
   .op .AND]

def newpart26Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := UInt256.land v2 x3
  {s with pc := N 5122, memory := s.memory, stack := v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: v1 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart26_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart26Program {s with pc := N 5112, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart26Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart26Program, newpart26Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart27Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨7, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩)]

def newpart27Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := x7 - x0
  let v1 : W := x14 + v0
  {s with pc := N 5132, memory := s.memory, stack := v1 :: (N 2048) :: x14 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem newpart27_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart27Program {s with pc := N 5122, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (newpart27Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart27Program, newpart27Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart28Program : List Instr :=
  [.op .MULMOD,
   .push 2 128,
   .op .MLOAD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨9, by decide⟩)]

def newpart28Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord s.memory 128
  let v2 : W := UInt256.mulMod x11 v1 x16
  {s with pc := N 5142, memory := s.memory, stack := x10 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: v2 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart28_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) (hk_x1 : x1 = N 2048) :
    runInstructions newpart28Program {s with pc := N 5132, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart28Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hk_x1, hz, hzn, newpart28Program, newpart28Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128]


def newpart29Program : List Instr :=
  [.op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL]

def newpart29Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x11 * x1
  let v1 : W := x2 + v0
  let v2 : W := x15 * x6
  {s with pc := N 5150, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart29_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart29Program {s with pc := N 5142, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart29Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart29Program, newpart29Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart30Program : List Instr :=
  [.op .ADD,
   .push 2 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newpart30Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 224
  let v2 : W := UInt256.land v1 v0
  let v3 : W := x10 + x2
  {s with pc := N 5160, memory := s.memory, stack := x6 :: x16 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: v2 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart30_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart30Program {s with pc := N 5150, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart30Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart30Program, newpart30Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart31Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 7 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Swap ⟨3, by decide⟩)]

def newpart31Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x15 x0 x1
  let v1 : W := v0 + x2
  {s with pc := N 5175, memory := s.memory, stack := v1 :: x10 :: x16 :: (N 2048) :: x16 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart31_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart31Program {s with pc := N 5160, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart31Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart31Program, newpart31Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart32Program : List Instr :=
  [.op .SUB,
   .op .ADD,
   .op .MULMOD,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

def newpart32Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 - x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod v1 x3 x4
  {s with pc := N 5183, memory := s.memory, stack := x8 :: x9 :: x10 :: x11 :: x12 :: v2 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart32_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) (hk_x3 : x3 = N 2048) :
    runInstructions newpart32Program {s with pc := N 5175, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart32Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hk_x3, hz, hzn, newpart32Program, newpart32Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart33Program : List Instr :=
  [.op .POP]

def newpart33Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : W) (rest : List W) : State :=
  {s with pc := N 5184, memory := s.memory, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest}

theorem newpart33_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart33Program {s with pc := N 5183, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: rest} =
      some (newpart33Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 11) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart33Program, newpart33Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
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
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
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
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .push 2 224,
   .op .MLOAD,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
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
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
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
   .op (.Swap ⟨6, by decide⟩),
   .op .POP,
   .push 2 224,
   .op .MLOAD,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨6, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨7, by decide⟩),
   .op .POP,
   .push 2 224,
   .op .MLOAD,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨7, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨14, by decide⟩),
   .op .ADD,
   .push 2 2048,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .push 2 128,
   .op .MLOAD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .op (.Dup ⟨10, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 2 224,
   .op .MLOAD,
   .op .AND,
   .op (.Swap ⟨8, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 7 2048,
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
   .op .POP]

def newModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := x6 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := x7 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 64
  let v7 : W := x8 * v6
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 32
  let v10 : W := x9 * v9
  let v11 : W := v10 + v8
  let v12 : W := x3 * x13
  let v13 : W := v12 + v11
  let v14 : W := x2 * x12
  let v15 : W := v14 + v13
  let v16 : W := x1 * x11
  let v17 : W := v16 + v15
  let v18 : W := x4 * x10
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 128
  let v21 : W := UInt256.mulMod x6 v20 x14
  let v22 : W := v21 + x0
  let v23 : W := MachineState.readWord s.memory 96
  let v24 : W := UInt256.mulMod x7 v23 x14
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 64
  let v27 : W := UInt256.mulMod x8 v26 x14
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 32
  let v30 : W := UInt256.mulMod x9 v29 x14
  let v31 : W := v30 + v28
  let v32 : W := UInt256.mulMod x3 x13 x14
  let v33 : W := v32 + v31
  let v34 : W := UInt256.mulMod x2 x12 x14
  let v35 : W := v34 + v33
  let v36 : W := UInt256.mulMod x1 x11 x14
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod x4 x10 x14
  let v39 : W := v38 + v37
  let v40 : W := MachineState.readWord s.memory 224
  let v41 : W := UInt256.land v40 v19
  let v42 : W := v39 - v41
  let v43 : W := x14 + v42
  let v44 : W := UInt256.mulMod v43 (N 2048) x14
  let v45 : W := MachineState.readWord s.memory 128
  let v46 : W := x7 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord s.memory 96
  let v49 : W := x8 * v48
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord s.memory 64
  let v52 : W := x9 * v51
  let v53 : W := v52 + v50
  let v54 : W := x2 * x13
  let v55 : W := v54 + v53
  let v56 : W := x1 * x12
  let v57 : W := v56 + v55
  let v58 : W := x4 * x11
  let v59 : W := v58 + v57
  let v60 : W := MachineState.readWord s.memory 128
  let v61 : W := UInt256.mulMod x7 v60 x14
  let v62 : W := v61 + v44
  let v63 : W := MachineState.readWord s.memory 96
  let v64 : W := UInt256.mulMod x8 v63 x14
  let v65 : W := v64 + v62
  let v66 : W := MachineState.readWord s.memory 64
  let v67 : W := UInt256.mulMod x9 v66 x14
  let v68 : W := v67 + v65
  let v69 : W := UInt256.mulMod x2 x13 x14
  let v70 : W := v69 + v68
  let v71 : W := UInt256.mulMod x1 x12 x14
  let v72 : W := v71 + v70
  let v73 : W := UInt256.mulMod x4 x11 x14
  let v74 : W := v73 + v72
  let v75 : W := MachineState.readWord s.memory 224
  let v76 : W := UInt256.land v75 v59
  let v77 : W := v74 - v76
  let v78 : W := x14 + v77
  let v79 : W := UInt256.mulMod v78 (N 2048) x14
  let v80 : W := MachineState.readWord s.memory 128
  let v81 : W := x8 * v80
  let v82 : W := v81 + v79
  let v83 : W := MachineState.readWord s.memory 96
  let v84 : W := x9 * v83
  let v85 : W := v84 + v82
  let v86 : W := x1 * x13
  let v87 : W := v86 + v85
  let v88 : W := x4 * x12
  let v89 : W := v88 + v87
  let v90 : W := MachineState.readWord s.memory 128
  let v91 : W := UInt256.mulMod x8 v90 x14
  let v92 : W := v91 + v79
  let v93 : W := MachineState.readWord s.memory 96
  let v94 : W := UInt256.mulMod x9 v93 x14
  let v95 : W := v94 + v92
  let v96 : W := UInt256.mulMod x1 x13 x14
  let v97 : W := v96 + v95
  let v98 : W := UInt256.mulMod x4 x12 x14
  let v99 : W := v98 + v97
  let v100 : W := MachineState.readWord s.memory 224
  let v101 : W := UInt256.land v100 v89
  let v102 : W := v99 - v101
  let v103 : W := x14 + v102
  let v104 : W := UInt256.mulMod v103 (N 2048) x14
  let v105 : W := MachineState.readWord s.memory 128
  let v106 : W := UInt256.mulMod x9 v105 x14
  let v107 : W := x9 * v105
  let v108 : W := v104 + v107
  let v109 : W := x13 * x4
  let v110 : W := v109 + v108
  let v111 : W := MachineState.readWord s.memory 224
  let v112 : W := UInt256.land v111 v110
  let v113 : W := v106 + v104
  let v114 : W := UInt256.mulMod x13 x4 x14
  let v115 : W := v114 + v113
  let v116 : W := v115 - v112
  let v117 : W := v116 + x14
  let v118 : W := UInt256.mulMod v117 (N 2048) x14
  {s with pc := N 5184, memory := s.memory, stack := v41 :: v76 :: v101 :: v112 :: v118 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem new_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 962) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := N 4874, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (newModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := x6 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := x7 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 64
  let v7 : W := x8 * v6
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 32
  let v10 : W := x9 * v9
  let v11 : W := v10 + v8
  let v12 : W := x3 * x13
  let v13 : W := v12 + v11
  let v14 : W := x2 * x12
  let v15 : W := v14 + v13
  let v16 : W := x1 * x11
  let v17 : W := v16 + v15
  let v18 : W := x4 * x10
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 128
  let v21 : W := UInt256.mulMod x6 v20 x14
  let v22 : W := v21 + x0
  let v23 : W := MachineState.readWord s.memory 96
  let v24 : W := UInt256.mulMod x7 v23 x14
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 64
  let v27 : W := UInt256.mulMod x8 v26 x14
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 32
  let v30 : W := UInt256.mulMod x9 v29 x14
  let v31 : W := v30 + v28
  let v32 : W := UInt256.mulMod x3 x13 x14
  let v33 : W := v32 + v31
  let v34 : W := UInt256.mulMod x2 x12 x14
  let v35 : W := v34 + v33
  let v36 : W := UInt256.mulMod x1 x11 x14
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod x4 x10 x14
  let v39 : W := v38 + v37
  let v40 : W := MachineState.readWord s.memory 224
  let v41 : W := UInt256.land v40 v19
  let v42 : W := v39 - v41
  let v43 : W := x14 + v42
  let v44 : W := UInt256.mulMod v43 (N 2048) x14
  let v45 : W := MachineState.readWord s.memory 128
  let v46 : W := x7 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord s.memory 96
  let v49 : W := x8 * v48
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord s.memory 64
  let v52 : W := x9 * v51
  let v53 : W := v52 + v50
  let v54 : W := x2 * x13
  let v55 : W := v54 + v53
  let v56 : W := x1 * x12
  let v57 : W := v56 + v55
  let v58 : W := x4 * x11
  let v59 : W := v58 + v57
  let v60 : W := MachineState.readWord s.memory 128
  let v61 : W := UInt256.mulMod x7 v60 x14
  let v62 : W := v61 + v44
  let v63 : W := MachineState.readWord s.memory 96
  let v64 : W := UInt256.mulMod x8 v63 x14
  let v65 : W := v64 + v62
  let v66 : W := MachineState.readWord s.memory 64
  let v67 : W := UInt256.mulMod x9 v66 x14
  let v68 : W := v67 + v65
  let v69 : W := UInt256.mulMod x2 x13 x14
  let v70 : W := v69 + v68
  let v71 : W := UInt256.mulMod x1 x12 x14
  let v72 : W := v71 + v70
  let v73 : W := UInt256.mulMod x4 x11 x14
  let v74 : W := v73 + v72
  let v75 : W := MachineState.readWord s.memory 224
  let v76 : W := UInt256.land v75 v59
  let v77 : W := v74 - v76
  let v78 : W := x14 + v77
  let v79 : W := UInt256.mulMod v78 (N 2048) x14
  let v80 : W := MachineState.readWord s.memory 128
  let v81 : W := x8 * v80
  let v82 : W := v81 + v79
  let v83 : W := MachineState.readWord s.memory 96
  let v84 : W := x9 * v83
  let v85 : W := v84 + v82
  let v86 : W := x1 * x13
  let v87 : W := v86 + v85
  let v88 : W := x4 * x12
  let v89 : W := v88 + v87
  let v90 : W := MachineState.readWord s.memory 128
  let v91 : W := UInt256.mulMod x8 v90 x14
  let v92 : W := v91 + v79
  let v93 : W := MachineState.readWord s.memory 96
  let v94 : W := UInt256.mulMod x9 v93 x14
  let v95 : W := v94 + v92
  let v96 : W := UInt256.mulMod x1 x13 x14
  let v97 : W := v96 + v95
  let v98 : W := UInt256.mulMod x4 x12 x14
  let v99 : W := v98 + v97
  let v100 : W := MachineState.readWord s.memory 224
  let v101 : W := UInt256.land v100 v89
  let v102 : W := v99 - v101
  let v103 : W := x14 + v102
  let v104 : W := UInt256.mulMod v103 (N 2048) x14
  let v105 : W := MachineState.readWord s.memory 128
  let v106 : W := UInt256.mulMod x9 v105 x14
  let v107 : W := x9 * v105
  let v108 : W := v104 + v107
  let v109 : W := x13 * x4
  let v110 : W := v109 + v108
  let v111 : W := MachineState.readWord s.memory 224
  let v112 : W := UInt256.land v111 v110
  let v113 : W := v106 + v104
  let v114 : W := UInt256.mulMod x13 x4 x14
  let v115 : W := v114 + v113
  let v116 : W := v115 - v112
  let v117 : W := v116 + x14
  let v118 : W := UInt256.mulMod v117 (N 2048) x14
  have h0 : runInstructions newpart0Program {s with pc := N 4874, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4885, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart0Model, v0, v1, v2, v3] using newpart0_run (s) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h1 : runInstructions newpart1Program {s with pc := N 4885, memory := s.memory, stack := v3 :: v2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4894, memory := s.memory, stack := v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart1Model, v4, v5, v6, v7, v8] using newpart1_run (s) (v3) (v2) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h2 : runInstructions newpart2Program {s with pc := N 4894, memory := s.memory, stack := v8 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4903, memory := s.memory, stack := v12 :: v11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart2Model, v9, v10, v11, v12] using newpart2_run (s) (v8) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h3 : runInstructions newpart3Program {s with pc := N 4903, memory := s.memory, stack := v12 :: v11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4911, memory := s.memory, stack := v16 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart3Model, v13, v14, v15, v16] using newpart3_run (s) (v12) (v11) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h4 : runInstructions newpart4Program {s with pc := N 4911, memory := s.memory, stack := v16 :: v15 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4921, memory := s.memory, stack := v20 :: x14 :: x0 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart4Model, v17, v18, v19, v20] using newpart4_run (s) (v16) (v15) (x0) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h5 : runInstructions newpart5Program {s with pc := N 4921, memory := s.memory, stack := v20 :: x14 :: x0 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4930, memory := s.memory, stack := v24 :: v22 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart5Model, v21, v22, v23, v24] using newpart5_run (s) (v20) (x14) (x0) (v19) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h6 : runInstructions newpart6Program {s with pc := N 4930, memory := s.memory, stack := v24 :: v22 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4939, memory := s.memory, stack := x14 :: v28 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart6Model, v25, v26, v27, v28] using newpart6_run (s) (v24) (v22) (v19) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h7 : runInstructions newpart7Program {s with pc := N 4939, memory := s.memory, stack := x14 :: v28 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4948, memory := s.memory, stack := x3 :: x13 :: x14 :: v31 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart7Model, v29, v30, v31] using newpart7_run (s) (x14) (v28) (v19) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h8 : runInstructions newpart8Program {s with pc := N 4948, memory := s.memory, stack := x3 :: x13 :: x14 :: v31 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4956, memory := s.memory, stack := x14 :: v35 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart8Model, v32, v33, v34, v35] using newpart8_run (s) (x3) (x13) (x14) (v31) (v19) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h9 : runInstructions newpart9Program {s with pc := N 4956, memory := s.memory, stack := x14 :: v35 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4964, memory := s.memory, stack := v38 :: v37 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart9Model, v36, v37, v38] using newpart9_run (s) (x14) (v35) (v19) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h10 : runInstructions newpart10Program {s with pc := N 4964, memory := s.memory, stack := v38 :: v37 :: v19 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4974, memory := s.memory, stack := v39 :: v41 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart10Model, v39, v40, v41] using newpart10_run (s) (v38) (v37) (v19) (x1) (x2) (x3) (x4) (x5) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h11 : runInstructions newpart11Program {s with pc := N 4974, memory := s.memory, stack := v39 :: v41 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4984, memory := s.memory, stack := v44 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart11Model, v42, v43, v44] using newpart11_run (s) (v39) (v41) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h12 : runInstructions newpart12Program {s with pc := N 4984, memory := s.memory, stack := v44 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 4994, memory := s.memory, stack := x8 :: v48 :: v47 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart12Model, v45, v46, v47, v48] using newpart12_run (s) (v44) (v44) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h13 : runInstructions newpart13Program {s with pc := N 4994, memory := s.memory, stack := x8 :: v48 :: v47 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5003, memory := s.memory, stack := x13 :: v53 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart13Model, v49, v50, v51, v52, v53] using newpart13_run (s) (x8) (v48) (v47) (v44) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h14 : runInstructions newpart14Program {s with pc := N 5003, memory := s.memory, stack := x13 :: v53 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5011, memory := s.memory, stack := x11 :: v57 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart14Model, v54, v55, v56, v57] using newpart14_run (s) (x13) (v53) (v44) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h15 : runInstructions newpart15Program {s with pc := N 5011, memory := s.memory, stack := x11 :: v57 :: v44 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5020, memory := s.memory, stack := x7 :: v60 :: x14 :: v44 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart15Model, v58, v59, v60] using newpart15_run (s) (x11) (v57) (v44) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h16 : runInstructions newpart16Program {s with pc := N 5020, memory := s.memory, stack := x7 :: v60 :: x14 :: v44 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5029, memory := s.memory, stack := v65 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart16Model, v61, v62, v63, v64, v65] using newpart16_run (s) (x7) (v60) (x14) (v44) (v59) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h17 : runInstructions newpart17Program {s with pc := N 5029, memory := s.memory, stack := v65 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5038, memory := s.memory, stack := x13 :: x14 :: v68 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart17Model, v66, v67, v68] using newpart17_run (s) (v65) (v59) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h18 : runInstructions newpart18Program {s with pc := N 5038, memory := s.memory, stack := x13 :: x14 :: v68 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5046, memory := s.memory, stack := v72 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart18Model, v69, v70, v71, v72] using newpart18_run (s) (x13) (x14) (v68) (v59) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h19 : runInstructions newpart19Program {s with pc := N 5046, memory := s.memory, stack := v72 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5057, memory := s.memory, stack := v75 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: v74 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart19Model, v73, v74, v75] using newpart19_run (s) (v72) (v59) (x1) (x2) (x3) (x4) (v41) (x6) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h20 : runInstructions newpart20Program {s with pc := N 5057, memory := s.memory, stack := v75 :: v59 :: x1 :: x2 :: x3 :: x4 :: v41 :: v74 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5067, memory := s.memory, stack := x14 :: (N 2048) :: v78 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart20Model, v76, v77, v78] using newpart20_run (s) (v75) (v59) (x1) (x2) (x3) (x4) (v41) (v74) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h21 : runInstructions newpart21Program {s with pc := N 5067, memory := s.memory, stack := x14 :: (N 2048) :: v78 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5076, memory := s.memory, stack := v82 :: v79 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart21Model, v79, v80, v81, v82] using newpart21_run (s) (x14) ((N 2048)) (v78) (x1) (x2) (x3) (x4) (v41) (v76) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact (by rfl)
  have h22 : runInstructions newpart22Program {s with pc := N 5076, memory := s.memory, stack := v82 :: v79 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5085, memory := s.memory, stack := v86 :: v85 :: v79 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart22Model, v83, v84, v85, v86] using newpart22_run (s) (v82) (v79) (x1) (x2) (x3) (x4) (v41) (v76) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h23 : runInstructions newpart23Program {s with pc := N 5085, memory := s.memory, stack := v86 :: v85 :: v79 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5095, memory := s.memory, stack := v90 :: x14 :: v79 :: v89 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart23Model, v87, v88, v89, v90] using newpart23_run (s) (v86) (v85) (v79) (x1) (x2) (x3) (x4) (v41) (v76) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h24 : runInstructions newpart24Program {s with pc := N 5095, memory := s.memory, stack := v90 :: x14 :: v79 :: v89 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5104, memory := s.memory, stack := v94 :: v92 :: v89 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart24Model, v91, v92, v93, v94] using newpart24_run (s) (v90) (x14) (v79) (v89) (x1) (x2) (x3) (x4) (v41) (v76) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h25 : runInstructions newpart25Program {s with pc := N 5104, memory := s.memory, stack := v94 :: v92 :: v89 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5112, memory := s.memory, stack := x12 :: x14 :: v97 :: v89 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart25Model, v95, v96, v97] using newpart25_run (s) (v94) (v92) (v89) (x1) (x2) (x3) (x4) (v41) (v76) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h26 : runInstructions newpart26Program {s with pc := N 5112, memory := s.memory, stack := x12 :: x14 :: v97 :: v89 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5122, memory := s.memory, stack := v101 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v99 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart26Model, v98, v99, v100, v101] using newpart26_run (s) (x12) (x14) (v97) (v89) (x1) (x2) (x3) (x4) (v41) (v76) (x7) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h27 : runInstructions newpart27Program {s with pc := N 5122, memory := s.memory, stack := v101 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v99 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5132, memory := s.memory, stack := v103 :: (N 2048) :: x14 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart27Model, v102, v103] using newpart27_run (s) (v101) (x1) (x2) (x3) (x4) (v41) (v76) (v99) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h28 : runInstructions newpart28Program {s with pc := N 5132, memory := s.memory, stack := v103 :: (N 2048) :: x14 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5142, memory := s.memory, stack := x8 :: v105 :: v104 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v106 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart28Model, v104, v105, v106] using newpart28_run (s) (v103) ((N 2048)) (x14) (x1) (x2) (x3) (x4) (v41) (v76) (v101) (x8) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact (by rfl)
  have h29 : runInstructions newpart29Program {s with pc := N 5142, memory := s.memory, stack := x8 :: v105 :: v104 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v106 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5150, memory := s.memory, stack := v109 :: v108 :: v104 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v106 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart29Model, v107, v108, v109] using newpart29_run (s) (x8) (v105) (v104) (x1) (x2) (x3) (x4) (v41) (v76) (v101) (v106) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h30 : runInstructions newpart30Program {s with pc := N 5150, memory := s.memory, stack := v109 :: v108 :: v104 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v106 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5160, memory := s.memory, stack := x4 :: x14 :: v113 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v112 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart30Model, v110, v111, v112, v113] using newpart30_run (s) (v109) (v108) (v104) (x1) (x2) (x3) (x4) (v41) (v76) (v101) (v106) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h31 : runInstructions newpart31Program {s with pc := N 5160, memory := s.memory, stack := x4 :: x14 :: v113 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v112 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5175, memory := s.memory, stack := v115 :: v112 :: x14 :: (N 2048) :: x14 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v112 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart31Model, v114, v115] using newpart31_run (s) (x4) (x14) (v113) (x1) (x2) (x3) (x4) (v41) (v76) (v101) (v112) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  have h32 : runInstructions newpart32Program {s with pc := N 5175, memory := s.memory, stack := v115 :: v112 :: x14 :: (N 2048) :: x14 :: x1 :: x2 :: x3 :: x4 :: v41 :: v76 :: v101 :: v112 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5183, memory := s.memory, stack := x4 :: v41 :: v76 :: v101 :: v112 :: v118 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart32Model, v116, v117, v118] using newpart32_run (s) (v115) (v112) (x14) ((N 2048)) (x14) (x1) (x2) (x3) (x4) (v41) (v76) (v101) (v112) (x9) (x10) (x11) (x12) (x13) (x14) rest hcap hact (by rfl)
  have h33 : runInstructions newpart33Program {s with pc := N 5183, memory := s.memory, stack := x4 :: v41 :: v76 :: v101 :: v112 :: v118 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} = some {s with pc := N 5184, memory := s.memory, stack := v41 :: v76 :: v101 :: v112 :: v118 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} := by
    simpa only [newpart33Model] using newpart33_run (s) (x4) (v41) (v76) (v101) (v112) (v118) (x10) (x11) (x12) (x13) (x14) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 (runInstructions_append_some _ _ _ _ _ h21 (runInstructions_append_some _ _ _ _ _ h22 (runInstructions_append_some _ _ _ _ _ h23 (runInstructions_append_some _ _ _ _ _ h24 (runInstructions_append_some _ _ _ _ _ h25 (runInstructions_append_some _ _ _ _ _ h26 (runInstructions_append_some _ _ _ _ _ h27 (runInstructions_append_some _ _ _ _ _ h28 (runInstructions_append_some _ _ _ _ _ h29 (runInstructions_append_some _ _ _ _ _ h30 (runInstructions_append_some _ _ _ _ _ h31 (runInstructions_append_some _ _ _ _ _ h32 h33)))))))))))))))))))))))))))))))))

#print axioms new_run

def oldModel (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := x6 * v0
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 96
  let v4 : W := x7 * v3
  let v5 : W := v4 + v2
  let v6 : W := MachineState.readWord s.memory 64
  let v7 : W := x8 * v6
  let v8 : W := v7 + v5
  let v9 : W := MachineState.readWord s.memory 32
  let v10 : W := x9 * v9
  let v11 : W := v10 + v8
  let v12 : W := x3 * x13
  let v13 : W := v12 + v11
  let v14 : W := x2 * x12
  let v15 : W := v14 + v13
  let v16 : W := x1 * x11
  let v17 : W := v16 + v15
  let v18 : W := x4 * x10
  let v19 : W := v18 + v17
  let v20 : W := MachineState.readWord s.memory 128
  let v21 : W := UInt256.mulMod x6 v20 x14
  let v22 : W := v21 + x0
  let v23 : W := MachineState.readWord s.memory 96
  let v24 : W := UInt256.mulMod x7 v23 x14
  let v25 : W := v24 + v22
  let v26 : W := MachineState.readWord s.memory 64
  let v27 : W := UInt256.mulMod x8 v26 x14
  let v28 : W := v27 + v25
  let v29 : W := MachineState.readWord s.memory 32
  let v30 : W := UInt256.mulMod x9 v29 x14
  let v31 : W := v30 + v28
  let v32 : W := UInt256.mulMod x3 x13 x14
  let v33 : W := v32 + v31
  let v34 : W := UInt256.mulMod x2 x12 x14
  let v35 : W := v34 + v33
  let v36 : W := UInt256.mulMod x1 x11 x14
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod x4 x10 x14
  let v39 : W := v38 + v37
  let v40 : W := MachineState.readWord s.memory 224
  let v41 : W := UInt256.land v40 v19
  let v42 : W := v39 - v41
  let v43 : W := x14 + v42
  let v44 : W := UInt256.mulMod v43 (N 2048) x14
  let v45 : W := MachineState.readWord s.memory 128
  let v46 : W := x7 * v45
  let v47 : W := v46 + v44
  let v48 : W := MachineState.readWord s.memory 96
  let v49 : W := x8 * v48
  let v50 : W := v49 + v47
  let v51 : W := MachineState.readWord s.memory 64
  let v52 : W := x9 * v51
  let v53 : W := v52 + v50
  let v54 : W := x2 * x13
  let v55 : W := v54 + v53
  let v56 : W := x1 * x12
  let v57 : W := v56 + v55
  let v58 : W := x4 * x11
  let v59 : W := v58 + v57
  let v60 : W := MachineState.readWord s.memory 128
  let v61 : W := UInt256.mulMod x7 v60 x14
  let v62 : W := v61 + v44
  let v63 : W := MachineState.readWord s.memory 96
  let v64 : W := UInt256.mulMod x8 v63 x14
  let v65 : W := v64 + v62
  let v66 : W := MachineState.readWord s.memory 64
  let v67 : W := UInt256.mulMod x9 v66 x14
  let v68 : W := v67 + v65
  let v69 : W := UInt256.mulMod x2 x13 x14
  let v70 : W := v69 + v68
  let v71 : W := UInt256.mulMod x1 x12 x14
  let v72 : W := v71 + v70
  let v73 : W := UInt256.mulMod x4 x11 x14
  let v74 : W := v73 + v72
  let v75 : W := MachineState.readWord s.memory 224
  let v76 : W := UInt256.land v75 v59
  let v77 : W := v74 - v76
  let v78 : W := x14 + v77
  let v79 : W := UInt256.mulMod v78 (N 2048) x14
  let v80 : W := MachineState.readWord s.memory 128
  let v81 : W := x8 * v80
  let v82 : W := v81 + v79
  let v83 : W := MachineState.readWord s.memory 96
  let v84 : W := x9 * v83
  let v85 : W := v84 + v82
  let v86 : W := x1 * x13
  let v87 : W := v86 + v85
  let v88 : W := x4 * x12
  let v89 : W := v88 + v87
  let v90 : W := MachineState.readWord s.memory 128
  let v91 : W := UInt256.mulMod x8 v90 x14
  let v92 : W := v91 + v79
  let v93 : W := MachineState.readWord s.memory 96
  let v94 : W := UInt256.mulMod x9 v93 x14
  let v95 : W := v94 + v92
  let v96 : W := UInt256.mulMod x1 x13 x14
  let v97 : W := v96 + v95
  let v98 : W := UInt256.mulMod x4 x12 x14
  let v99 : W := v98 + v97
  let v100 : W := MachineState.readWord s.memory 224
  let v101 : W := UInt256.land v100 v89
  let v102 : W := v99 - v101
  let v103 : W := x14 + v102
  let v104 : W := UInt256.mulMod v103 (N 2048) x14
  let v105 : W := MachineState.readWord s.memory 128
  let v106 : W := x9 * v105
  let v107 : W := v106 + v104
  let v108 : W := x4 * x13
  let v109 : W := v108 + v107
  let v110 : W := MachineState.readWord s.memory 128
  let v111 : W := UInt256.mulMod x9 v110 x14
  let v112 : W := v111 + v104
  let v113 : W := UInt256.mulMod x4 x13 x14
  let v114 : W := v113 + v112
  let v115 : W := MachineState.readWord s.memory 224
  let v116 : W := UInt256.land v115 v109
  let v117 : W := v114 - v116
  let v118 : W := x14 + v117
  let v119 : W := UInt256.mulMod v118 (N 2048) x14
  {s with pc := N 5184, memory := s.memory, stack := v41 :: v76 :: v101 :: v116 :: v119 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

private theorem aux_shared0 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared1 (x4 x13 : W) :
    (x13 * x4) = (x4 * x13) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared2 (x4 x13 x14 : W) :
    (UInt256.mulMod x13 x4 x14) = (UInt256.mulMod x4 x13 x14) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

private theorem aux_shared3 (x14 : W) (z0 : W) :
    (z0 + x14) = (x14 + z0) := by
  simp only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC]

theorem same_state (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) :
    oldModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest = newModel s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest := by
  let o0 : W := MachineState.readWord s.memory 128
  let o1 : W := x6 * o0
  let o2 : W := o1 + x0
  let o3 : W := MachineState.readWord s.memory 96
  let o4 : W := x7 * o3
  let o5 : W := o4 + o2
  let o6 : W := MachineState.readWord s.memory 64
  let o7 : W := x8 * o6
  let o8 : W := o7 + o5
  let o9 : W := MachineState.readWord s.memory 32
  let o10 : W := x9 * o9
  let o11 : W := o10 + o8
  let o12 : W := x3 * x13
  let o13 : W := o12 + o11
  let o14 : W := x2 * x12
  let o15 : W := o14 + o13
  let o16 : W := x1 * x11
  let o17 : W := o16 + o15
  let o18 : W := x4 * x10
  let o19 : W := o18 + o17
  let o20 : W := MachineState.readWord s.memory 128
  let o21 : W := UInt256.mulMod x6 o20 x14
  let o22 : W := o21 + x0
  let o23 : W := MachineState.readWord s.memory 96
  let o24 : W := UInt256.mulMod x7 o23 x14
  let o25 : W := o24 + o22
  let o26 : W := MachineState.readWord s.memory 64
  let o27 : W := UInt256.mulMod x8 o26 x14
  let o28 : W := o27 + o25
  let o29 : W := MachineState.readWord s.memory 32
  let o30 : W := UInt256.mulMod x9 o29 x14
  let o31 : W := o30 + o28
  let o32 : W := UInt256.mulMod x3 x13 x14
  let o33 : W := o32 + o31
  let o34 : W := UInt256.mulMod x2 x12 x14
  let o35 : W := o34 + o33
  let o36 : W := UInt256.mulMod x1 x11 x14
  let o37 : W := o36 + o35
  let o38 : W := UInt256.mulMod x4 x10 x14
  let o39 : W := o38 + o37
  let o40 : W := MachineState.readWord s.memory 224
  let o41 : W := UInt256.land o40 o19
  let o42 : W := o39 - o41
  let o43 : W := x14 + o42
  let o44 : W := UInt256.mulMod o43 (N 2048) x14
  let o45 : W := MachineState.readWord s.memory 128
  let o46 : W := x7 * o45
  let o47 : W := o46 + o44
  let o48 : W := MachineState.readWord s.memory 96
  let o49 : W := x8 * o48
  let o50 : W := o49 + o47
  let o51 : W := MachineState.readWord s.memory 64
  let o52 : W := x9 * o51
  let o53 : W := o52 + o50
  let o54 : W := x2 * x13
  let o55 : W := o54 + o53
  let o56 : W := x1 * x12
  let o57 : W := o56 + o55
  let o58 : W := x4 * x11
  let o59 : W := o58 + o57
  let o60 : W := MachineState.readWord s.memory 128
  let o61 : W := UInt256.mulMod x7 o60 x14
  let o62 : W := o61 + o44
  let o63 : W := MachineState.readWord s.memory 96
  let o64 : W := UInt256.mulMod x8 o63 x14
  let o65 : W := o64 + o62
  let o66 : W := MachineState.readWord s.memory 64
  let o67 : W := UInt256.mulMod x9 o66 x14
  let o68 : W := o67 + o65
  let o69 : W := UInt256.mulMod x2 x13 x14
  let o70 : W := o69 + o68
  let o71 : W := UInt256.mulMod x1 x12 x14
  let o72 : W := o71 + o70
  let o73 : W := UInt256.mulMod x4 x11 x14
  let o74 : W := o73 + o72
  let o75 : W := MachineState.readWord s.memory 224
  let o76 : W := UInt256.land o75 o59
  let o77 : W := o74 - o76
  let o78 : W := x14 + o77
  let o79 : W := UInt256.mulMod o78 (N 2048) x14
  let o80 : W := MachineState.readWord s.memory 128
  let o81 : W := x8 * o80
  let o82 : W := o81 + o79
  let o83 : W := MachineState.readWord s.memory 96
  let o84 : W := x9 * o83
  let o85 : W := o84 + o82
  let o86 : W := x1 * x13
  let o87 : W := o86 + o85
  let o88 : W := x4 * x12
  let o89 : W := o88 + o87
  let o90 : W := MachineState.readWord s.memory 128
  let o91 : W := UInt256.mulMod x8 o90 x14
  let o92 : W := o91 + o79
  let o93 : W := MachineState.readWord s.memory 96
  let o94 : W := UInt256.mulMod x9 o93 x14
  let o95 : W := o94 + o92
  let o96 : W := UInt256.mulMod x1 x13 x14
  let o97 : W := o96 + o95
  let o98 : W := UInt256.mulMod x4 x12 x14
  let o99 : W := o98 + o97
  let o100 : W := MachineState.readWord s.memory 224
  let o101 : W := UInt256.land o100 o89
  let o102 : W := o99 - o101
  let o103 : W := x14 + o102
  let o104 : W := UInt256.mulMod o103 (N 2048) x14
  let o105 : W := MachineState.readWord s.memory 128
  let o106 : W := x9 * o105
  let o107 : W := o106 + o104
  let o108 : W := x4 * x13
  let o109 : W := o108 + o107
  let o110 : W := MachineState.readWord s.memory 128
  let o111 : W := UInt256.mulMod x9 o110 x14
  let o112 : W := o111 + o104
  let o113 : W := UInt256.mulMod x4 x13 x14
  let o114 : W := o113 + o112
  let o115 : W := MachineState.readWord s.memory 224
  let o116 : W := UInt256.land o115 o109
  let o117 : W := o114 - o116
  let o118 : W := x14 + o117
  let o119 : W := UInt256.mulMod o118 (N 2048) x14
  let n0 : W := MachineState.readWord s.memory 128
  let n1 : W := x6 * n0
  let n2 : W := n1 + x0
  let n3 : W := MachineState.readWord s.memory 96
  let n4 : W := x7 * n3
  let n5 : W := n4 + n2
  let n6 : W := MachineState.readWord s.memory 64
  let n7 : W := x8 * n6
  let n8 : W := n7 + n5
  let n9 : W := MachineState.readWord s.memory 32
  let n10 : W := x9 * n9
  let n11 : W := n10 + n8
  let n12 : W := x3 * x13
  let n13 : W := n12 + n11
  let n14 : W := x2 * x12
  let n15 : W := n14 + n13
  let n16 : W := x1 * x11
  let n17 : W := n16 + n15
  let n18 : W := x4 * x10
  let n19 : W := n18 + n17
  let n20 : W := MachineState.readWord s.memory 128
  let n21 : W := UInt256.mulMod x6 n20 x14
  let n22 : W := n21 + x0
  let n23 : W := MachineState.readWord s.memory 96
  let n24 : W := UInt256.mulMod x7 n23 x14
  let n25 : W := n24 + n22
  let n26 : W := MachineState.readWord s.memory 64
  let n27 : W := UInt256.mulMod x8 n26 x14
  let n28 : W := n27 + n25
  let n29 : W := MachineState.readWord s.memory 32
  let n30 : W := UInt256.mulMod x9 n29 x14
  let n31 : W := n30 + n28
  let n32 : W := UInt256.mulMod x3 x13 x14
  let n33 : W := n32 + n31
  let n34 : W := UInt256.mulMod x2 x12 x14
  let n35 : W := n34 + n33
  let n36 : W := UInt256.mulMod x1 x11 x14
  let n37 : W := n36 + n35
  let n38 : W := UInt256.mulMod x4 x10 x14
  let n39 : W := n38 + n37
  let n40 : W := MachineState.readWord s.memory 224
  let n41 : W := UInt256.land n40 n19
  let n42 : W := n39 - n41
  let n43 : W := x14 + n42
  let n44 : W := UInt256.mulMod n43 (N 2048) x14
  let n45 : W := MachineState.readWord s.memory 128
  let n46 : W := x7 * n45
  let n47 : W := n46 + n44
  let n48 : W := MachineState.readWord s.memory 96
  let n49 : W := x8 * n48
  let n50 : W := n49 + n47
  let n51 : W := MachineState.readWord s.memory 64
  let n52 : W := x9 * n51
  let n53 : W := n52 + n50
  let n54 : W := x2 * x13
  let n55 : W := n54 + n53
  let n56 : W := x1 * x12
  let n57 : W := n56 + n55
  let n58 : W := x4 * x11
  let n59 : W := n58 + n57
  let n60 : W := MachineState.readWord s.memory 128
  let n61 : W := UInt256.mulMod x7 n60 x14
  let n62 : W := n61 + n44
  let n63 : W := MachineState.readWord s.memory 96
  let n64 : W := UInt256.mulMod x8 n63 x14
  let n65 : W := n64 + n62
  let n66 : W := MachineState.readWord s.memory 64
  let n67 : W := UInt256.mulMod x9 n66 x14
  let n68 : W := n67 + n65
  let n69 : W := UInt256.mulMod x2 x13 x14
  let n70 : W := n69 + n68
  let n71 : W := UInt256.mulMod x1 x12 x14
  let n72 : W := n71 + n70
  let n73 : W := UInt256.mulMod x4 x11 x14
  let n74 : W := n73 + n72
  let n75 : W := MachineState.readWord s.memory 224
  let n76 : W := UInt256.land n75 n59
  let n77 : W := n74 - n76
  let n78 : W := x14 + n77
  let n79 : W := UInt256.mulMod n78 (N 2048) x14
  let n80 : W := MachineState.readWord s.memory 128
  let n81 : W := x8 * n80
  let n82 : W := n81 + n79
  let n83 : W := MachineState.readWord s.memory 96
  let n84 : W := x9 * n83
  let n85 : W := n84 + n82
  let n86 : W := x1 * x13
  let n87 : W := n86 + n85
  let n88 : W := x4 * x12
  let n89 : W := n88 + n87
  let n90 : W := MachineState.readWord s.memory 128
  let n91 : W := UInt256.mulMod x8 n90 x14
  let n92 : W := n91 + n79
  let n93 : W := MachineState.readWord s.memory 96
  let n94 : W := UInt256.mulMod x9 n93 x14
  let n95 : W := n94 + n92
  let n96 : W := UInt256.mulMod x1 x13 x14
  let n97 : W := n96 + n95
  let n98 : W := UInt256.mulMod x4 x12 x14
  let n99 : W := n98 + n97
  let n100 : W := MachineState.readWord s.memory 224
  let n101 : W := UInt256.land n100 n89
  let n102 : W := n99 - n101
  let n103 : W := x14 + n102
  let n104 : W := UInt256.mulMod n103 (N 2048) x14
  let n105 : W := MachineState.readWord s.memory 128
  let n106 : W := UInt256.mulMod x9 n105 x14
  let n107 : W := x9 * n105
  let n108 : W := n104 + n107
  let n109 : W := x13 * x4
  let n110 : W := n109 + n108
  let n111 : W := MachineState.readWord s.memory 224
  let n112 : W := UInt256.land n111 n110
  let n113 : W := n106 + n104
  let n114 : W := UInt256.mulMod x13 x4 x14
  let n115 : W := n114 + n113
  let n116 : W := n115 - n112
  let n117 : W := n116 + x14
  let n118 : W := UInt256.mulMod n117 (N 2048) x14
  have eq_o20 : o20 = o0 := by
    simp only [o20, o0]
  have eq_o23 : o23 = o3 := by
    simp only [o23, o3]
  have eq_o26 : o26 = o6 := by
    simp only [o26, o6]
  have eq_o29 : o29 = o9 := by
    simp only [o29, o9]
  have eq_o45 : o45 = o0 := by
    simp only [o45, o0]
  have eq_o48 : o48 = o3 := by
    simp only [o48, o3]
  have eq_o51 : o51 = o6 := by
    simp only [o51, o6]
  have eq_o60 : o60 = o0 := by
    simp only [o60, o0]
  have eq_o63 : o63 = o3 := by
    simp only [o63, o3]
  have eq_o66 : o66 = o6 := by
    simp only [o66, o6]
  have eq_o75 : o75 = o40 := by
    simp only [o75, o40]
  have eq_o80 : o80 = o0 := by
    simp only [o80, o0]
  have eq_o83 : o83 = o3 := by
    simp only [o83, o3]
  have eq_o90 : o90 = o0 := by
    simp only [o90, o0]
  have eq_o93 : o93 = o3 := by
    simp only [o93, o3]
  have eq_o100 : o100 = o40 := by
    simp only [o100, o40]
  have eq_o105 : o105 = o0 := by
    simp only [o105, o0]
  have eq_o110 : o110 = o0 := by
    simp only [o110, o0]
  have eq_o115 : o115 = o40 := by
    simp only [o115, o40]
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4, eq_n2]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7, eq_n5]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10, eq_n9]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n10, eq_n8]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n12, eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14, eq_n13]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n16, eq_n15]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18, eq_n17]
  have eq_n20 : n20 = o0 := by
    simp only [n20, o0]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20, eq_o20]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21]
  have eq_n23 : n23 = o3 := by
    simp only [n23, o3]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n23, eq_o23]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n24, eq_n22]
  have eq_n26 : n26 = o6 := by
    simp only [n26, o6]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n26, eq_o26]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27, eq_n25]
  have eq_n29 : n29 = o9 := by
    simp only [n29, o9]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n29, eq_o29]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n30, eq_n28]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n32, eq_n31]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34, eq_n33]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36, eq_n35]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n38, eq_n37]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n40, eq_n19]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n39, eq_n41]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n42]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n43]
  have eq_n45 : n45 = o0 := by
    simp only [n45, o0]
  have eq_n46 : n46 = o46 := by
    simp only [n46, o46, eq_n45, eq_o45]
  have eq_n47 : n47 = o47 := by
    simp only [n47, o47, eq_n46, eq_n44]
  have eq_n48 : n48 = o3 := by
    simp only [n48, o3]
  have eq_n49 : n49 = o49 := by
    simp only [n49, o49, eq_n48, eq_o48]
  have eq_n50 : n50 = o50 := by
    simp only [n50, o50, eq_n49, eq_n47]
  have eq_n51 : n51 = o6 := by
    simp only [n51, o6]
  have eq_n52 : n52 = o52 := by
    simp only [n52, o52, eq_n51, eq_o51]
  have eq_n53 : n53 = o53 := by
    simp only [n53, o53, eq_n52, eq_n50]
  have eq_n54 : n54 = o54 := by
    simp only [n54, o54]
  have eq_n55 : n55 = o55 := by
    simp only [n55, o55, eq_n54, eq_n53]
  have eq_n56 : n56 = o56 := by
    simp only [n56, o56]
  have eq_n57 : n57 = o57 := by
    simp only [n57, o57, eq_n56, eq_n55]
  have eq_n58 : n58 = o58 := by
    simp only [n58, o58]
  have eq_n59 : n59 = o59 := by
    simp only [n59, o59, eq_n58, eq_n57]
  have eq_n60 : n60 = o0 := by
    simp only [n60, o0]
  have eq_n61 : n61 = o61 := by
    simp only [n61, o61, eq_n60, eq_o60]
  have eq_n62 : n62 = o62 := by
    simp only [n62, o62, eq_n61, eq_n44]
  have eq_n63 : n63 = o3 := by
    simp only [n63, o3]
  have eq_n64 : n64 = o64 := by
    simp only [n64, o64, eq_n63, eq_o63]
  have eq_n65 : n65 = o65 := by
    simp only [n65, o65, eq_n64, eq_n62]
  have eq_n66 : n66 = o6 := by
    simp only [n66, o6]
  have eq_n67 : n67 = o67 := by
    simp only [n67, o67, eq_n66, eq_o66]
  have eq_n68 : n68 = o68 := by
    simp only [n68, o68, eq_n67, eq_n65]
  have eq_n69 : n69 = o69 := by
    simp only [n69, o69]
  have eq_n70 : n70 = o70 := by
    simp only [n70, o70, eq_n69, eq_n68]
  have eq_n71 : n71 = o71 := by
    simp only [n71, o71]
  have eq_n72 : n72 = o72 := by
    simp only [n72, o72, eq_n71, eq_n70]
  have eq_n73 : n73 = o73 := by
    simp only [n73, o73]
  have eq_n74 : n74 = o74 := by
    simp only [n74, o74, eq_n73, eq_n72]
  have eq_n75 : n75 = o40 := by
    simp only [n75, o40]
  have eq_n76 : n76 = o76 := by
    simp only [n76, o76, eq_n75, eq_n59, eq_o75]
  have eq_n77 : n77 = o77 := by
    simp only [n77, o77, eq_n74, eq_n76]
  have eq_n78 : n78 = o78 := by
    simp only [n78, o78, eq_n77]
  have eq_n79 : n79 = o79 := by
    simp only [n79, o79, eq_n78]
  have eq_n80 : n80 = o0 := by
    simp only [n80, o0]
  have eq_n81 : n81 = o81 := by
    simp only [n81, o81, eq_n80, eq_o80]
  have eq_n82 : n82 = o82 := by
    simp only [n82, o82, eq_n81, eq_n79]
  have eq_n83 : n83 = o3 := by
    simp only [n83, o3]
  have eq_n84 : n84 = o84 := by
    simp only [n84, o84, eq_n83, eq_o83]
  have eq_n85 : n85 = o85 := by
    simp only [n85, o85, eq_n84, eq_n82]
  have eq_n86 : n86 = o86 := by
    simp only [n86, o86]
  have eq_n87 : n87 = o87 := by
    simp only [n87, o87, eq_n86, eq_n85]
  have eq_n88 : n88 = o88 := by
    simp only [n88, o88]
  have eq_n89 : n89 = o89 := by
    simp only [n89, o89, eq_n88, eq_n87]
  have eq_n90 : n90 = o0 := by
    simp only [n90, o0]
  have eq_n91 : n91 = o91 := by
    simp only [n91, o91, eq_n90, eq_o90]
  have eq_n92 : n92 = o92 := by
    simp only [n92, o92, eq_n91, eq_n79]
  have eq_n93 : n93 = o3 := by
    simp only [n93, o3]
  have eq_n94 : n94 = o94 := by
    simp only [n94, o94, eq_n93, eq_o93]
  have eq_n95 : n95 = o95 := by
    simp only [n95, o95, eq_n94, eq_n92]
  have eq_n96 : n96 = o96 := by
    simp only [n96, o96]
  have eq_n97 : n97 = o97 := by
    simp only [n97, o97, eq_n96, eq_n95]
  have eq_n98 : n98 = o98 := by
    simp only [n98, o98]
  have eq_n99 : n99 = o99 := by
    simp only [n99, o99, eq_n98, eq_n97]
  have eq_n100 : n100 = o40 := by
    simp only [n100, o40]
  have eq_n101 : n101 = o101 := by
    simp only [n101, o101, eq_n100, eq_n89, eq_o100]
  have eq_n102 : n102 = o102 := by
    simp only [n102, o102, eq_n99, eq_n101]
  have eq_n103 : n103 = o103 := by
    simp only [n103, o103, eq_n102]
  have eq_n104 : n104 = o104 := by
    simp only [n104, o104, eq_n103]
  have eq_n105 : n105 = o0 := by
    simp only [n105, o0]
  have eq_n106 : n106 = o111 := by
    simp only [n106, o111, eq_n105, eq_o110]
  have eq_n107 : n107 = o106 := by
    simp only [n107, o106, eq_n105, eq_o105]
  have eq_n108 : n108 = o107 := by
    simpa only [n108, o107, eq_n104, eq_n107] using
      (aux_shared0  o104 o106)
  have eq_n109 : n109 = o108 := by
    simpa only [n109, o108] using
      (aux_shared1 x4 x13 )
  have eq_n110 : n110 = o109 := by
    simp only [n110, o109, eq_n109, eq_n108]
  have eq_n111 : n111 = o40 := by
    simp only [n111, o40]
  have eq_n112 : n112 = o116 := by
    simp only [n112, o116, eq_n111, eq_n110, eq_o115]
  have eq_n113 : n113 = o112 := by
    simp only [n113, o112, eq_n106, eq_n104]
  have eq_n114 : n114 = o113 := by
    simpa only [n114, o113] using
      (aux_shared2 x4 x13 x14 )
  have eq_n115 : n115 = o114 := by
    simp only [n115, o114, eq_n114, eq_n113]
  have eq_n116 : n116 = o117 := by
    simp only [n116, o117, eq_n115, eq_n112]
  have eq_n117 : n117 = o118 := by
    simpa only [n117, o118, eq_n116] using
      (aux_shared3 x14 o117)
  have eq_n118 : n118 = o119 := by
    simp only [n118, o119, eq_n117]
  change {s with pc := N 5184, memory := s.memory, stack := o41 :: o76 :: o101 :: o116 :: o119 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
    {s with pc := N 5184, memory := s.memory, stack := n41 :: n76 :: n101 :: n112 :: n118 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}
  simp only [eq_o20, eq_o23, eq_o26, eq_o29, eq_o45, eq_o48, eq_o51, eq_o60, eq_o63, eq_o66, eq_o75, eq_o80, eq_o83, eq_o90, eq_o93, eq_o100, eq_o105, eq_o110, eq_o115, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51, eq_n52, eq_n53, eq_n54, eq_n55, eq_n56, eq_n57, eq_n58, eq_n59, eq_n60, eq_n61, eq_n62, eq_n63, eq_n64, eq_n65, eq_n66, eq_n67, eq_n68, eq_n69, eq_n70, eq_n71, eq_n72, eq_n73, eq_n74, eq_n75, eq_n76, eq_n77, eq_n78, eq_n79, eq_n80, eq_n81, eq_n82, eq_n83, eq_n84, eq_n85, eq_n86, eq_n87, eq_n88, eq_n89, eq_n90, eq_n91, eq_n92, eq_n93, eq_n94, eq_n95, eq_n96, eq_n97, eq_n98, eq_n99, eq_n100, eq_n101, eq_n102, eq_n103, eq_n104, eq_n105, eq_n106, eq_n107, eq_n108, eq_n109, eq_n110, eq_n111, eq_n112, eq_n113, eq_n114, eq_n115, eq_n116, eq_n117, eq_n118]

#print axioms same_state
end CycleSubmission.Prepared.R5Product
