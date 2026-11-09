import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInputLate
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

def dbl13p0Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def dbl13p0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x14 * x8
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7371, memory := s.memory, stack := x7 :: x10 :: x2 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem dbl13p0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p0Program {s with pc := UInt256.ofNat 7363, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (dbl13p0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p0Program, dbl13p0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p1Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def dbl13p1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x12 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x10 x7 x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7379, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl13p1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p1Program {s with pc := UInt256.ofNat 7371, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl13p1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p1Program, dbl13p1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p2Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def dbl13p2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x11 x3 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 7387, memory := s.memory, stack := x13 :: x7 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl13p2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p2Program {s with pc := UInt256.ofNat 7379, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl13p2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p2Program, dbl13p2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p3Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .MSTORE]

def dbl13p3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 64
  {s with pc := UInt256.ofNat 7396, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem dbl13p3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p3Program {s with pc := UInt256.ofNat 7387, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (dbl13p3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl13p3Program, dbl13p3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha64, hf64]

def dbl13p4Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 8 2048,
   .op .MULMOD]

def dbl13p4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x9
  {s with pc := UInt256.ofNat 7411, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl13p4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p4Program {s with pc := UInt256.ofNat 7396, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl13p4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p4Program, dbl13p4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p5Program : List Instr :=
  [.push 2 832,
   .op .MLOAD,
   .op (.Swap ⟨5, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD]

def dbl13p5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord (s.memory) 832
  let v1 : UInt256 := MachineState.readWord (s.memory) 128
  {s with pc := UInt256.ofNat 7422, memory := s.memory, stack := v1 :: x8 :: x14 :: x0 :: x1 :: x2 :: x3 :: x4 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem dbl13p5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p5Program {s with pc := UInt256.ofNat 7411, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (dbl13p5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha832 : (832 : UInt256).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl13p5Program, dbl13p5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha832, ha128, hf832, hf128]

def dbl13p6Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨2, by decide⟩)]

def dbl13p6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := x2 * v0
  let v2 : UInt256 := UInt256.mulMod x2 v0 x1
  {s with pc := UInt256.ofNat 7430, memory := s.memory, stack := x3 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl13p6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p6Program {s with pc := UInt256.ofNat 7422, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl13p6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p6Program, dbl13p6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p7Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD]

def dbl13p7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := x3 + x2
  let v2 : UInt256 := MachineState.readWord (s.memory) 160
  let v3 : UInt256 := v2 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7439, memory := s.memory, stack := v4 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl13p7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p7Program {s with pc := UInt256.ofNat 7430, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl13p7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl13p7Program, dbl13p7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha160, hf160]

def dbl13p8Program : List Instr :=
  [.op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def dbl13p8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x10 * x5
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x8 * x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7447, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl13p8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p8Program {s with pc := UInt256.ofNat 7439, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl13p8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p8Program, dbl13p8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p9Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def dbl13p9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x13 * x3
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord (s.memory) 160
  {s with pc := UInt256.ofNat 7456, memory := s.memory, stack := v2 :: x9 :: x1 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl13p9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p9Program {s with pc := UInt256.ofNat 7447, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl13p9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl13p9Program, dbl13p9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha160, hf160]

def dbl13p10Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def dbl13p10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x12 x7 x11
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7464, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem dbl13p10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p10Program {s with pc := UInt256.ofNat 7456, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (dbl13p10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p10Program, dbl13p10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p11Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def dbl13p11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x11 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 7472, memory := s.memory, stack := x3 :: x13 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl13p11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p11Program {s with pc := UInt256.ofNat 7464, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl13p11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p11Program, dbl13p11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13p12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 96,
   .op .MSTORE]

def dbl13p12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.land x15 x4
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 96
  {s with pc := UInt256.ofNat 7481, memory := v3, stack := v2 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem dbl13p12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p12Program {s with pc := UInt256.ofNat 7472, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (dbl13p12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, capacity,dbl13p12Program, dbl13p12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ha96, hf96]

def dbl13p13Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩),
   .op .ADD,
   .push 10 2048,
   .op .MULMOD]

def dbl13p13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x1 - x0
  let v1 : UInt256 := x9 + v0
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x9
  {s with pc := UInt256.ofNat 7498, memory := s.memory, stack := v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem dbl13p13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13p13Program {s with pc := UInt256.ofNat 7481, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (dbl13p13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have capacity (j : Nat) (hj : j ≤ 30) : rest.length+j < 1024 := by omega
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  simp [hz, hzn, capacity,dbl13p13Program, dbl13p13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, ]

def dbl13Program : List Instr := dbl13p0Program ++ (dbl13p1Program ++ (dbl13p2Program ++ (dbl13p3Program ++ (dbl13p4Program ++ (dbl13p5Program ++ (dbl13p6Program ++ (dbl13p7Program ++ (dbl13p8Program ++ (dbl13p9Program ++ (dbl13p10Program ++ (dbl13p11Program ++ (dbl13p12Program ++ (dbl13p13Program)))))))))))))

def dbl13Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry + w0
  let v1 : UInt256 := w13 * w7
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := UInt256.mulMod w10 w6 w9
  let v4 : UInt256 := v3 + w1
  let v5 : UInt256 := UInt256.mulMod w8 w5 w9
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod w11 w3 w9
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod w13 w7 w9
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : UInt256 := v10 - v11
  let v14 : UInt256 := w9 + v13
  let v15 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v14 w9
  let v16 : UInt256 := MachineState.readWord (v12) 832
  let v17 : UInt256 := MachineState.readWord (v12) 128
  let v18 : UInt256 := v17 + v17
  let v19 : UInt256 := w15 * v18
  let v20 : UInt256 := UInt256.mulMod w15 v18 w9
  let v21 : UInt256 := v15 + v20
  let v22 : UInt256 := v15 + v19
  let v23 : UInt256 := MachineState.readWord (v12) 160
  let v24 : UInt256 := v23 * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := w10 * w5
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := w8 * w11
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := w13 * w3
  let v31 : UInt256 := v30 + v29
  let v32 : UInt256 := MachineState.readWord (v12) 160
  let v33 : UInt256 := UInt256.mulMod v32 v32 w9
  let v34 : UInt256 := v33 + v21
  let v35 : UInt256 := UInt256.mulMod w10 w5 w9
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := UInt256.mulMod w8 w11 w9
  let v38 : UInt256 := v37 + v36
  let v39 : UInt256 := UInt256.mulMod w3 w13 w9
  let v40 : UInt256 := v39 + v38
  let v41 : UInt256 := UInt256.land w12 v31
  let v42 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v41.toNat 32) 96
  let v43 : UInt256 := v40 - v41
  let v44 : UInt256 := w9 + v43
  let v45 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v44 w9
  {s with pc := UInt256.ofNat 7498, memory := v42, stack := v45 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem dbl13_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15: W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions dbl13Program {s with pc := N 7363, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (dbl13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : UInt256 := carry + w0
  let v1 : UInt256 := w13 * w7
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := UInt256.mulMod w10 w6 w9
  let v4 : UInt256 := v3 + w1
  let v5 : UInt256 := UInt256.mulMod w8 w5 w9
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := UInt256.mulMod w11 w3 w9
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.mulMod w13 w7 w9
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : UInt256 := v10 - v11
  let v14 : UInt256 := w9 + v13
  let v15 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v14 w9
  let v16 : UInt256 := MachineState.readWord (v12) 832
  let v17 : UInt256 := MachineState.readWord (v12) 128
  let v18 : UInt256 := v17 + v17
  let v19 : UInt256 := w15 * v18
  let v20 : UInt256 := UInt256.mulMod w15 v18 w9
  let v21 : UInt256 := v15 + v20
  let v22 : UInt256 := v15 + v19
  let v23 : UInt256 := MachineState.readWord (v12) 160
  let v24 : UInt256 := v23 * v23
  let v25 : UInt256 := v24 + v22
  let v26 : UInt256 := w10 * w5
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := w8 * w11
  let v29 : UInt256 := v28 + v27
  let v30 : UInt256 := w13 * w3
  let v31 : UInt256 := v30 + v29
  let v32 : UInt256 := MachineState.readWord (v12) 160
  let v33 : UInt256 := UInt256.mulMod v32 v32 w9
  let v34 : UInt256 := v33 + v21
  let v35 : UInt256 := UInt256.mulMod w10 w5 w9
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := UInt256.mulMod w8 w11 w9
  let v38 : UInt256 := v37 + v36
  let v39 : UInt256 := UInt256.mulMod w3 w13 w9
  let v40 : UInt256 := v39 + v38
  let v41 : UInt256 := UInt256.land w12 v31
  let v42 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v41.toNat 32) 96
  let v43 : UInt256 := v40 - v41
  let v44 : UInt256 := w9 + v43
  let v45 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v44 w9
  have h0 : runInstructions dbl13p0Program {s with pc := N 7363, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7371, memory := s.memory, stack := w6 :: w9 :: w1 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p0Model, v0, v1, v2] using
      dbl13p0_run ({s with memory := s.memory}) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions dbl13p1Program {s with pc := N 7371, memory := s.memory, stack := w6 :: w9 :: w1 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7379, memory := s.memory, stack := v6 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p1Model, v3, v4, v5, v6] using
      dbl13p1_run ({s with memory := s.memory}) (w6) (w9) (w1) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions dbl13p2Program {s with pc := N 7379, memory := s.memory, stack := v6 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7387, memory := s.memory, stack := w13 :: w7 :: w9 :: v8 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p2Model, v7, v8] using
      dbl13p2_run ({s with memory := s.memory}) (v6) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions dbl13p3Program {s with pc := N 7387, memory := s.memory, stack := w13 :: w7 :: w9 :: v8 :: v2 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7396, memory := v12, stack := v11 :: v10 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p3Model, v9, v10, v11, v12] using
      dbl13p3_run ({s with memory := s.memory}) (w13) (w7) (w9) (v8) (v2) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions dbl13p4Program {s with pc := N 7396, memory := v12, stack := v11 :: v10 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7411, memory := v12, stack := v15 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p4Model, v13, v14, v15] using
      dbl13p4_run ({s with memory := v12}) (v11) (v10) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions dbl13p5Program {s with pc := N 7411, memory := v12, stack := v15 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7422, memory := v12, stack := v17 :: w9 :: w15 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p5Model, v16, v17] using
      dbl13p5_run ({s with memory := v12}) (v15) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions dbl13p6Program {s with pc := N 7422, memory := v12, stack := v17 :: w9 :: w15 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7430, memory := v12, stack := v15 :: v20 :: v19 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p6Model, v18, v19, v20] using
      dbl13p6_run ({s with memory := v12}) (v17) (w9) (w15) (v15) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h7 : runInstructions dbl13p7Program {s with pc := N 7430, memory := v12, stack := v15 :: v20 :: v19 :: v15 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7439, memory := v12, stack := v25 :: v21 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p7Model, v21, v22, v23, v24, v25] using
      dbl13p7_run ({s with memory := v12}) (v15) (v20) (v19) (v15) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h8 : runInstructions dbl13p8Program {s with pc := N 7439, memory := v12, stack := v25 :: v21 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7447, memory := v12, stack := v29 :: v21 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p8Model, v26, v27, v28, v29] using
      dbl13p8_run ({s with memory := v12}) (v25) (v21) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h9 : runInstructions dbl13p9Program {s with pc := N 7447, memory := v12, stack := v29 :: v21 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7456, memory := v12, stack := v32 :: w9 :: v21 :: v31 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p9Model, v30, v31, v32] using
      dbl13p9_run ({s with memory := v12}) (v29) (v21) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h10 : runInstructions dbl13p10Program {s with pc := N 7456, memory := v12, stack := v32 :: w9 :: v21 :: v31 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7464, memory := v12, stack := v36 :: v31 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p10Model, v33, v34, v35, v36] using
      dbl13p10_run ({s with memory := v12}) (v32) (w9) (v21) (v31) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h11 : runInstructions dbl13p11Program {s with pc := N 7464, memory := v12, stack := v36 :: v31 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7472, memory := v12, stack := w3 :: w13 :: w9 :: v38 :: v31 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p11Model, v37, v38] using
      dbl13p11_run ({s with memory := v12}) (v36) (v31) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h12 : runInstructions dbl13p12Program {s with pc := N 7472, memory := v12, stack := w3 :: w13 :: w9 :: v38 :: v31 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7481, memory := v42, stack := v41 :: v40 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p12Model, v39, v40, v41, v42] using
      dbl13p12_run ({s with memory := v12}) (w3) (w13) (w9) (v38) (v31) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h13 : runInstructions dbl13p13Program {s with pc := N 7481, memory := v42, stack := v41 :: v40 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 7498, memory := v42, stack := v45 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [dbl13p13Model, v43, v44, v45] using
      dbl13p13_run ({s with memory := v42}) (v41) (v40) (w2) (w3) (w4) (w5) (v16) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  change runInstructions dbl13Program _ = some _
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))

def sq13NewModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := w13 * w7
  let v2 : W := v1 + v0
  let v3 : W := UInt256.mulMod w10 w6 w9
  let v4 : W := v3 + w1
  let v5 : W := UInt256.mulMod w8 w5 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod w11 w3 w9
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod w13 w7 w9
  let v10 : W := v9 + v8
  let v11 : W := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : W := v10 - v11
  let v14 : W := w9 + v13
  let v15 : W := UInt256.mulMod (N 2048) v14 w9
  let v16 : W := MachineState.readWord v12 832
  let v17 : W := MachineState.readWord v12 128
  let v18 : W := w15 * v17
  let v19 : W := v18 + v18
  let v20 : W := UInt256.mulMod w15 v17 w9
  let v21 : W := v20 + v20
  let v22 : W := v15 + v21
  let v23 : W := v15 + v19
  let v24 : W := MachineState.readWord v12 160
  let v25 : W := v24 * v24
  let v26 : W := v25 + v23
  let v27 : W := w10 * w5
  let v28 : W := v27 + v26
  let v29 : W := w8 * w11
  let v30 : W := v29 + v28
  let v31 : W := w13 * w3
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord v12 160
  let v34 : W := UInt256.mulMod v33 v33 w9
  let v35 : W := v34 + v22
  let v36 : W := UInt256.mulMod w10 w5 w9
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w8 w11 w9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w3 w13 w9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.land w12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : W := v41 - v42
  let v45 : W := w9 + v44
  let v46 : W := UInt256.mulMod (N 2048) v45 w9
  {s with pc := N 7498, memory := v43, stack := v46 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}


def squareColumn13Model (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := carry + w0
  let v1 : W := w13 * w7
  let v2 : W := v1 + v0
  let v3 : W := UInt256.mulMod w10 w6 w9
  let v4 : W := v3 + w1
  let v5 : W := UInt256.mulMod w8 w5 w9
  let v6 : W := v5 + v4
  let v7 : W := UInt256.mulMod w11 w3 w9
  let v8 : W := v7 + v6
  let v9 : W := UInt256.mulMod w13 w7 w9
  let v10 : W := v9 + v8
  let v11 : W := UInt256.land w12 v2
  let v12 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v11.toNat 32) 64
  let v13 : W := v10 - v11
  let v14 : W := w9 + v13
  let v15 : W := UInt256.mulMod v14 (N 2048) w9
  let v16 : W := MachineState.readWord v12 832
  let v17 : W := MachineState.readWord v12 128
  let v18 : W := w15 * v17
  let v19 : W := v18 + v18
  let v20 : W := UInt256.mulMod w15 v17 w9
  let v21 : W := v20 + v20
  let v22 : W := v15 + v21
  let v23 : W := v15 + v19
  let v24 : W := MachineState.readWord v12 160
  let v25 : W := v24 * v24
  let v26 : W := v25 + v23
  let v27 : W := w10 * w5
  let v28 : W := v27 + v26
  let v29 : W := w8 * w11
  let v30 : W := v29 + v28
  let v31 : W := w13 * w3
  let v32 : W := v31 + v30
  let v33 : W := MachineState.readWord v12 160
  let v34 : W := UInt256.mulMod v33 v33 w9
  let v35 : W := v34 + v22
  let v36 : W := UInt256.mulMod w10 w5 w9
  let v37 : W := v36 + v35
  let v38 : W := UInt256.mulMod w8 w11 w9
  let v39 : W := v38 + v37
  let v40 : W := UInt256.mulMod w3 w13 w9
  let v41 : W := v40 + v39
  let v42 : W := UInt256.land w12 v32
  let v43 : ByteArray := MachineState.writeBytes v12 (Data.Bytes.natToBytesPadded v42.toNat 32) 96
  let v44 : W := v41 - v42
  let v45 : W := w9 + v44
  let v46 : W := UInt256.mulMod v45 (N 2048) w9
  {s with pc := N 7498, memory := v43, stack := v46 :: w2 :: w3 :: w4 :: w5 :: v16 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

def squareColumn13Program : List Instr := dbl13Program

#print axioms dbl13_run

/-- The shared-input late13 program has the same abstract result as the
previous double-product program. Only the changed input digit is bounded:
the preceding carry and every other high term are already MULMOD residues. -/
theorem dbl13_model_eq (s : State)
    (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W)
    (rest : List W) (hp : w9 = N (2^251-1)) (hm : w12 = N (2^240-1))
    (ha : (MachineState.readWord s.memory 128).toNat < 2^240) :
    dbl13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest =
      sq13NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  subst w9
  subst w12
  let p : W := N (2^251-1)
  let earlyDigit := UInt256.land (N (2^240-1)) (w13*w7+(carry+w0))
  let m := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded earlyDigit.toNat 32) 64
  let a := MachineState.readWord m 128
  let squareInput := MachineState.readWord m 160
  let c := UInt256.mulMod (N 2048)
    (p+((UInt256.mulMod w13 w7 p+
      (UInt256.mulMod w11 w3 p+(UInt256.mulMod w8 w5 p+
        (UInt256.mulMod w10 w6 p+w1))))-earlyDigit)) p
  let q0 := UInt256.mulMod squareInput squareInput p
  let q1 := UInt256.mulMod w10 w5 p
  let q2 := UInt256.mulMod w8 w11 p
  let q3 := UInt256.mulMod w3 w13 p
  let extra := q3+(q2+(q1+(q0+c)))
  let low := w13*w3+(w8*w11+(w10*w5+
    (squareInput*squareInput+(c+(w15*a+w15*a)))))
  let digit := UInt256.land (N (2^240-1)) low
  have hpv : p.toNat = 2^251-1 := by norm_num [p, word_toNat_ofNat]
  have hpos : 0 < p.toNat := by rw [hpv]; norm_num
  have hbudget : 8*p.toNat ≤ 2^256 := by rw [hpv]; norm_num
  have res_lt (x y : W) : (UInt256.mulMod x y p).toNat < p.toNat := by
    rw [CycleSubmission.DoubleInput.mulMod_nat _ _ _ hpos]
    exact Nat.mod_lt _ hpos
  have add_le (x y : W) : (x+y).toNat ≤ x.toNat+y.toNat := by
    rw [word_toNat_add]
    exact Nat.mod_le _ _
  have hroom : 3*p.toNat+extra.toNat ≤ 2^256 := by
    have hc : c.toNat < p.toNat := res_lt _ _
    have hq0 : q0.toNat < p.toNat := res_lt _ _
    have hq1 : q1.toNat < p.toNat := res_lt _ _
    have hq2 : q2.toNat < p.toNat := res_lt _ _
    have hq3 : q3.toNat < p.toNat := res_lt _ _
    have h0 := add_le q0 c
    have h1 := add_le q1 (q0+c)
    have h2 := add_le q2 (q1+(q0+c))
    have h3 := add_le q3 (q2+(q1+(q0+c)))
    dsimp only [extra]
    omega
  have ha' : a.toNat+a.toNat < 2^256 := by
    have hread : a = MachineState.readWord s.memory 128 := by
      dsimp only [a, m]
      exact read_disjoint _ _ 128 64 (by decide)
    rw [hread]
    omega
  have hd : digit.toNat < p.toNat := by
    dsimp only [digit]
    rw [HistoricalSearch.WordCancellation.land_comm]
    change (low &&& N (2^240-1)).toNat < p.toNat
    rw [HistoricalSearch.WordCancellation.mask_toNat _ 240 (by decide), hpv]
    have hx := Nat.mod_lt low.toNat (Nat.two_pow_pos 240)
    omega
  have hh : UInt256.mulMod (N 2048)
      (p+((q3+(q2+(q1+(q0+(c+UInt256.mulMod w15 (a+a) p)))))-digit)) p =
      UInt256.mulMod (N 2048)
        (p+((q3+(q2+(q1+(q0+(c+
          (UInt256.mulMod w15 a p+UInt256.mulMod w15 a p))))))-digit)) p := by
    simpa only [extra, addA] using
      (CycleSubmission.DoubleInput.high_double_biased_extra
        a w15 p extra digit (N 2048) hpos ha' hd hroom)
  simp only [p, a, squareInput, c, q0, q1, q2, q3, digit, low, m, earlyDigit] at hh
  simp only [dbl13Model, sq13NewModel, CycleSubmission.DoubleInput.low_double, hh]

#print axioms dbl13_model_eq

private theorem old_models_eq (s : State)
    (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W)
    (rest : List W) :
    sq13NewModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest =
      squareColumn13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  simp only [sq13NewModel, squareColumn13Model, addC, addA, addL, mulC, mmC]

/-- Execute late13 with the historical column-model output. No bound on the
incoming carry is needed: the changed column uses its own reduced carry. -/
theorem squareColumn13_run (s : State)
    (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W)
    (rest : List W) (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hp : w9 = N (2^251-1)) (hm : w12 = N (2^240-1))
    (ha : (MachineState.readWord s.memory 128).toNat < 2^240) :
    runInstructions squareColumn13Program
      {s with pc := N 7363, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (squareColumn13Model s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  exact (dbl13_run s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hcap hact).trans
    (congrArg some ((dbl13_model_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest hp hm ha).trans
      (old_models_eq s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest)))

#print axioms squareColumn13_run
end CycleSubmission.Execution
