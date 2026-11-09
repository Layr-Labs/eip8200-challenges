import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput
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

def dbl14p0Program : List Instr :=
  [.push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .push 2 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

def dbl14p0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord (s.memory) 800
  let v1 : UInt256 := MachineState.readWord (s.memory) 160
  {s with pc := UInt256.ofNat 7510, memory := s.memory, stack := v1 :: v1 :: x14 :: x0 :: x1 :: x2 :: x3 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem dbl14p0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p0Program {s with pc := UInt256.ofNat 7498, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (dbl14p0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl14p0Program, dbl14p0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha800, ha160, hf800, hf160]

def dbl14p1Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨2, by decide⟩)]

def dbl14p1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x2 v0 x11
  let v2 : UInt256 := x2 * v0
  {s with pc := UInt256.ofNat 7518, memory := s.memory, stack := x3 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl14p1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p1Program {s with pc := UInt256.ofNat 7510, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl14p1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p1Program, dbl14p1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p2Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL]

def dbl14p2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x13 * x12
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := x15 * x10
  {s with pc := UInt256.ofNat 7526, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl14p2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p2Program {s with pc := UInt256.ofNat 7518, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl14p2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p2Program, dbl14p2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p3Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def dbl14p3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x3 + x2
  let v2 : UInt256 := UInt256.mulMod x13 x12 x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7534, memory := s.memory, stack := v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl14p3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p3Program {s with pc := UInt256.ofNat 7526, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl14p3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p3Program, dbl14p3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p4Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND]

def dbl14p4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x13 x9
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.land x12 x1
  {s with pc := UInt256.ofNat 7542, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl14p4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p4Program {s with pc := UInt256.ofNat 7534, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl14p4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p4Program, dbl14p4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p5Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD]

def dbl14p5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 128
  let v1 : UInt256 := x1 - x0
  let v2 : UInt256 := x9 + v1
  {s with pc := UInt256.ofNat 7551, memory := v0, stack := v2 :: x9 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl14p5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p5Program {s with pc := UInt256.ofNat 7542, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl14p5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl14p5Program, dbl14p5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha128, hf128]

def dbl14p6Program : List Instr :=
  [.push 10 2048,
   .op .MULMOD,
   .op (.Swap ⟨9, by decide⟩),
   .op .POP,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD]

def dbl14p6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) x0 x1
  let v1 : UInt256 := UInt256.mulMod x13 x10 x9
  {s with pc := UInt256.ofNat 7569, memory := s.memory, stack := v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v0 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl14p6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p6Program {s with pc := UInt256.ofNat 7551, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl14p6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p6Program, dbl14p6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p7Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def dbl14p7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x14 x14 x8
  let v1 : UInt256 := x10 + v0
  let v2 : UInt256 := v1 + x0
  {s with pc := UInt256.ofNat 7577, memory := s.memory, stack := x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem dbl14p7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p7Program {s with pc := UInt256.ofNat 7569, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (dbl14p7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p7Program, dbl14p7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p8Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .push 3 1376,
   .op .MLOAD,
   .op (.Swap ⟨12, by decide⟩)]

def dbl14p8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x13 * x0
  let v1 : UInt256 := x15 * x15
  let v2 : UInt256 := MachineState.readWord (s.memory) 1376
  {s with pc := UInt256.ofNat 7588, memory := s.memory, stack := x11 :: v1 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v2 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl14p8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p8Program {s with pc := UInt256.ofNat 7577, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl14p8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl14p8Program, dbl14p8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha1376, hf1376]

def dbl14p9Program : List Instr :=
  [.op .ADD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 160,
   .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩)]

def dbl14p9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.land x14 v1
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 160
  {s with pc := UInt256.ofNat 7597, memory := v3, stack := x11 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl14p9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p9Program {s with pc := UInt256.ofNat 7588, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl14p9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl14p9Program, dbl14p9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha160, hf160]

def dbl14p10Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP]

def dbl14p10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 - x1
  let v1 : UInt256 := x0 + v0
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x0
  {s with pc := UInt256.ofNat 7613, memory := s.memory, stack := x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: v2 :: rest}

theorem dbl14p10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p10Program {s with pc := UInt256.ofNat 7597, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (dbl14p10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl14p10Program, dbl14p10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl14p11Program : List Instr :=
  [.push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP]

def dbl14p11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord (s.memory) 1344
  {s with pc := UInt256.ofNat 7619, memory := s.memory, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: v0 :: x12 :: x13 :: rest}

theorem dbl14p11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14p11Program {s with pc := UInt256.ofNat 7613, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (dbl14p11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl14p11Program, dbl14p11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha1344, hf1344]

def dbl14Program : List Instr := dbl14p0Program ++ (dbl14p1Program ++ (dbl14p2Program ++ (dbl14p3Program ++ (dbl14p4Program ++ (dbl14p5Program ++ (dbl14p6Program ++ (dbl14p7Program ++ (dbl14p8Program ++ (dbl14p9Program ++ (dbl14p10Program ++ (dbl14p11Program)))))))))))

def dbl14Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord (s.memory) 800
  let v1 : UInt256 := MachineState.readWord (s.memory) 160
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod w13 v2 w7
  let v4 : UInt256 := w13 * v2
  let v5 : UInt256 := carry + v4
  let v6 : UInt256 := w9 * w8
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := w11 * w6
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := carry + v3
  let v11 : UInt256 := UInt256.mulMod w9 w8 w7
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := UInt256.mulMod w6 w11 w7
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := UInt256.land w10 v9
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 128
  let v17 : UInt256 := v14 - v15
  let v18 : UInt256 := w7 + v17
  let v19 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v18 w7
  let v20 : UInt256 := UInt256.mulMod w11 w8 w7
  let v21 : UInt256 := UInt256.mulMod w13 w13 w7
  let v22 : UInt256 := v19 + v21
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := w11 * w8
  let v25 : UInt256 := w13 * w13
  let v26 : UInt256 := MachineState.readWord (v16) 1376
  let v27 : UInt256 := v19 + v25
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := UInt256.land w10 v28
  let v30 : ByteArray := MachineState.writeBytes v16 (Data.Bytes.natToBytesPadded v29.toNat 32) 160
  let v31 : UInt256 := v23 - v29
  let v32 : UInt256 := w7 + v31
  let v33 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v32 w7
  let v34 : UInt256 := MachineState.readWord (v30) 1344
  {s with pc := UInt256.ofNat 7619, memory := v30, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: v34 :: w12 :: v33 :: rest}

theorem dbl14_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13: W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl14Program {s with pc := N 7498, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (dbl14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  let v0 : UInt256 := MachineState.readWord (s.memory) 800
  let v1 : UInt256 := MachineState.readWord (s.memory) 160
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := UInt256.mulMod w13 v2 w7
  let v4 : UInt256 := w13 * v2
  let v5 : UInt256 := carry + v4
  let v6 : UInt256 := w9 * w8
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := w11 * w6
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := carry + v3
  let v11 : UInt256 := UInt256.mulMod w9 w8 w7
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := UInt256.mulMod w6 w11 w7
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := UInt256.land w10 v9
  let v16 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v15.toNat 32) 128
  let v17 : UInt256 := v14 - v15
  let v18 : UInt256 := w7 + v17
  let v19 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v18 w7
  let v20 : UInt256 := UInt256.mulMod w11 w8 w7
  let v21 : UInt256 := UInt256.mulMod w13 w13 w7
  let v22 : UInt256 := v19 + v21
  let v23 : UInt256 := v22 + v20
  let v24 : UInt256 := w11 * w8
  let v25 : UInt256 := w13 * w13
  let v26 : UInt256 := MachineState.readWord (v16) 1376
  let v27 : UInt256 := v19 + v25
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := UInt256.land w10 v28
  let v30 : ByteArray := MachineState.writeBytes v16 (Data.Bytes.natToBytesPadded v29.toNat 32) 160
  let v31 : UInt256 := v23 - v29
  let v32 : UInt256 := w7 + v31
  let v33 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v32 w7
  let v34 : UInt256 := MachineState.readWord (v30) 1344
  have h0 : runInstructions dbl14p0Program {s with pc := N 7498, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7510, memory := s.memory, stack := v1 :: v1 :: w13 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p0Model, v0, v1] using
      dbl14p0_run ({s with memory := s.memory}) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h1 : runInstructions dbl14p1Program {s with pc := N 7510, memory := s.memory, stack := v1 :: v1 :: w13 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7518, memory := s.memory, stack := carry :: v4 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p1Model, v2, v3, v4] using
      dbl14p1_run ({s with memory := s.memory}) (v1) (v1) (w13) (carry) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h2 : runInstructions dbl14p2Program {s with pc := N 7518, memory := s.memory, stack := carry :: v4 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7526, memory := s.memory, stack := v8 :: v7 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p2Model, v5, v6, v7, v8] using
      dbl14p2_run ({s with memory := s.memory}) (carry) (v4) (v3) (carry) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h3 : runInstructions dbl14p3Program {s with pc := N 7526, memory := s.memory, stack := v8 :: v7 :: v3 :: carry :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7534, memory := s.memory, stack := v12 :: v9 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p3Model, v9, v10, v11, v12] using
      dbl14p3_run ({s with memory := s.memory}) (v8) (v7) (v3) (carry) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h4 : runInstructions dbl14p4Program {s with pc := N 7534, memory := s.memory, stack := v12 :: v9 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7542, memory := s.memory, stack := v15 :: v14 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p4Model, v13, v14, v15] using
      dbl14p4_run ({s with memory := s.memory}) (v12) (v9) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h5 : runInstructions dbl14p5Program {s with pc := N 7542, memory := s.memory, stack := v15 :: v14 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7551, memory := v16, stack := v18 :: w7 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p5Model, v16, v17, v18] using
      dbl14p5_run ({s with memory := s.memory}) (v15) (v14) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h6 : runInstructions dbl14p6Program {s with pc := N 7551, memory := v16, stack := v18 :: w7 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7569, memory := v16, stack := v20 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p6Model, v19, v20] using
      dbl14p6_run ({s with memory := v16}) (v18) (w7) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) rest hcap hact
  have h7 : runInstructions dbl14p7Program {s with pc := N 7569, memory := v16, stack := v20 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7577, memory := v16, stack := w8 :: v23 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p7Model, v21, v22, v23] using
      dbl14p7_run ({s with memory := v16}) (v20) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) rest hcap hact
  have h8 : runInstructions dbl14p8Program {s with pc := N 7577, memory := v16, stack := w8 :: v23 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v19 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7588, memory := v16, stack := v19 :: v25 :: v24 :: v23 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p8Model, v24, v25, v26] using
      dbl14p8_run ({s with memory := v16}) (w8) (v23) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v19) (w10) (w11) (w12) (w13) rest hcap hact
  have h9 : runInstructions dbl14p9Program {s with pc := N 7588, memory := v16, stack := v19 :: v25 :: v24 :: v23 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7597, memory := v30, stack := w7 :: v29 :: v23 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: w11 :: w12 :: w13 :: rest} := by
    simpa only [dbl14p9Model, v27, v28, v29, v30] using
      dbl14p9_run ({s with memory := v16}) (v19) (v25) (v24) (v23) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v26) (w10) (w11) (w12) (w13) rest hcap hact
  have h10 : runInstructions dbl14p10Program {s with pc := N 7597, memory := v30, stack := w7 :: v29 :: v23 :: w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: w11 :: w12 :: w13 :: rest} = some {s with pc := N 7613, memory := v30, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: w11 :: w12 :: v33 :: rest} := by
    simpa only [dbl14p10Model, v31, v32, v33] using
      dbl14p10_run ({s with memory := v30}) (w7) (v29) (v23) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v26) (w10) (w11) (w12) (w13) rest hcap hact
  have h11 : runInstructions dbl14p11Program {s with pc := N 7613, memory := v30, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: w11 :: w12 :: v33 :: rest} = some {s with pc := N 7619, memory := v30, stack := w0 :: w1 :: w2 :: v0 :: w4 :: w5 :: w6 :: w7 :: w8 :: v26 :: w10 :: v34 :: w12 :: v33 :: rest} := by
    simpa only [dbl14p11Model, v34] using
      dbl14p11_run ({s with memory := v30}) (w0) (w1) (w2) (v0) (w4) (w5) (w6) (w7) (w8) (v26) (w10) (w11) (w12) (v33) rest hcap hact
  change runInstructions dbl14Program _ = some _
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 h11)))))))))))

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

def squareColumn14Program : List Instr := dbl14Program

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

#print axioms dbl14_run

theorem dbl14_model_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W)
    (rest : List W) (hp : w7 = N (2^251-1)) (hm : w10 = N (2^240-1))
    (hc : carry.toNat < w7.toNat)
    (ha : (MachineState.readWord s.memory 160).toNat < 2^240) :
    dbl14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest =
      sq14NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest := by
  subst w7
  subst w10
  let p : W := N (2^251-1)
  let a := MachineState.readWord s.memory 160
  let low := w11*w6+(w9*w8+(carry+(w13*a+w13*a)))
  let digit := UInt256.land (N (2^240-1)) low
  have hpv : p.toNat = 2^251-1 := by norm_num [p, word_toNat_ofNat]
  have hpos : 0 < p.toNat := by rw [hpv]; norm_num
  have hroom : 6*p.toNat ≤ 2^256 := by rw [hpv]; norm_num
  have res_lt (x y : W) : (UInt256.mulMod x y p).toNat < p.toNat := by
    rw [CycleSubmission.DoubleInput.mulMod_nat _ _ _ hpos]
    exact Nat.mod_lt _ hpos
  have hd : digit.toNat < p.toNat := by
    dsimp only [digit]
    rw [HistoricalSearch.WordCancellation.land_comm]
    change (low &&& N (2^240-1)).toNat < p.toNat
    rw [HistoricalSearch.WordCancellation.mask_toNat _ 240 (by decide), hpv]
    have hx := Nat.mod_lt low.toNat (Nat.two_pow_pos 240)
    omega
  have hh := CycleSubmission.DoubleInput.high_double_biased_column
    a w13 p carry (UInt256.mulMod w9 w8 p) (UInt256.mulMod w6 w11 p)
    digit (N 2048) hpos (by dsimp only [a]; omega) hc
    (res_lt _ _) (res_lt _ _) hd hroom
  simp only [p, a, digit, low] at hh
  simp only [dbl14Model, sq14NewModel, CycleSubmission.DoubleInput.low_double, hh]

#print axioms dbl14_model_eq

private theorem old_models_eq (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W)
    (rest : List W) :
    sq14NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest =
      squareColumn14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest := by
  simp (disch := decide) only [sq14NewModel, squareColumn14Model,
    addC, addA, addL, mulC, mmC, read_disjoint]

theorem squareColumn14_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : W)
    (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hp : w7 = N (2^251-1)) (hm : w10 = N (2^240-1))
    (hc : carry.toNat < w7.toNat)
    (ha : (MachineState.readWord s.memory 160).toNat < 2^240) :
    runInstructions squareColumn14Program
      {s with pc := N 7498, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: rest} =
      some (squareColumn14Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest) := by
  exact (dbl14_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hcap hact).trans
    (congrArg some ((dbl14_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest hp hm hc ha).trans
      (old_models_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 rest)))
#print axioms squareColumn14_run
end CycleSubmission.Execution
