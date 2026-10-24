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

def squareColumn10part0Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def squareColumn10part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x7 * x6
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7442, memory := s.memory, stack := x16 :: x13 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn10part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part0Program {s with pc := UInt256.ofNat 7434, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn10part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn10part0Program, squareColumn10part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn10part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn10part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x15 * x4
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7450, memory := s.memory, stack := x11 :: x3 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn10part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part1Program {s with pc := UInt256.ofNat 7442, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn10part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn10part1Program, squareColumn10part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn10part2Program : List Instr :=
  [.push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def squareColumn10part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := UInt256.mulMod v0 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 192
  {s with pc := UInt256.ofNat 7460, memory := s.memory, stack := v3 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn10part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part2Program {s with pc := UInt256.ofNat 7450, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn10part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part2Program, squareColumn10part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha192, hf192]


def squareColumn10part3Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD]

def squareColumn10part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x12 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := MachineState.readWord s.memory 0
  let v3 : UInt256 := UInt256.mulMod x10 v2 x11
  {s with pc := UInt256.ofNat 7468, memory := s.memory, stack := v3 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn10part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part3Program {s with pc := UInt256.ofNat 7460, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn10part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part3Program, squareColumn10part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def squareColumn10part4Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn10part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 224
  let v2 : UInt256 := UInt256.mulMod v1 x4 x10
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 7477, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn10part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part4Program {s with pc := UInt256.ofNat 7468, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn10part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part4Program, squareColumn10part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def squareColumn10part5Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD]

def squareColumn10part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x7 x8 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x6 x5 x10
  {s with pc := UInt256.ofNat 7485, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn10part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part5Program {s with pc := UInt256.ofNat 7477, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn10part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn10part5Program, squareColumn10part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn10part6Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def squareColumn10part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x12 x15 x10
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7493, memory := s.memory, stack := x3 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn10part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part6Program {s with pc := UInt256.ofNat 7485, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn10part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn10part6Program, squareColumn10part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn10part7Program : List Instr :=
  [.op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD]

def squareColumn10part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x15 x0 x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.lnot x3
  let v3 : UInt256 := UInt256.addMod v1 v2 x11
  {s with pc := UInt256.ofNat 7501, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn10part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part7Program {s with pc := UInt256.ofNat 7493, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn10part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn10part7Program, squareColumn10part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn10part8Program : List Instr :=
  [.push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 2 800,
   .op .MSTORE,
   .push 1 16]

def squareColumn10part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 5)
  let v1 : UInt256 := UInt256.land x12 x1
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 800
  {s with pc := UInt256.ofNat 7513, memory := v2, stack := (UInt256.ofNat 16) :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn10part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part8Program {s with pc := UInt256.ofNat 7501, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn10part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part8Program, squareColumn10part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha800, hf800]


def squareColumn10part9Program : List Instr :=
  [.op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD]

def squareColumn10part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 x0
  let v1 : UInt256 := UInt256.shiftRight x2 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 32
  {s with pc := UInt256.ofNat 7524, memory := s.memory, stack := v3 :: x10 :: x16 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn10part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part9Program {s with pc := UInt256.ofNat 7513, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn10part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part9Program, squareColumn10part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32]


def squareColumn10part10Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MUL]

def squareColumn10part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 * x0
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := MachineState.readWord s.memory 64
  let v3 : UInt256 := v2 * v1
  {s with pc := UInt256.ofNat 7534, memory := s.memory, stack := v3 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn10part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part10Program {s with pc := UInt256.ofNat 7524, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn10part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part10Program, squareColumn10part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha160, hf160]


def squareColumn10part11Program : List Instr :=
  [.op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn10part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 128
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := v2 * v1
  let v4 : UInt256 := v3 + v0
  {s with pc := UInt256.ofNat 7544, memory := s.memory, stack := v4 :: v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn10part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part11Program {s with pc := UInt256.ofNat 7534, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn10part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part11Program, squareColumn10part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha128, hf128]


def squareColumn10part12Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD]

def squareColumn10part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x4 x2 x3
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 64
  {s with pc := UInt256.ofNat 7554, memory := s.memory, stack := v3 :: v2 :: x13 :: v1 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn10part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part12Program {s with pc := UInt256.ofNat 7544, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn10part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part12Program, squareColumn10part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha160, hf160]


def squareColumn10part13Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD]

def squareColumn10part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 128
  let v3 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 7563, memory := s.memory, stack := v3 :: v2 :: x13 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn10part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10part13Program {s with pc := UInt256.ofNat 7554, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn10part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn10part13Program, squareColumn10part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha128, hf128]


def squareColumn10Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 2 800,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
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
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD]

def squareColumn10Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := word6 * word5
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := word15 * word12
  let v5 : UInt256 := v4 + v3
  let v6 : UInt256 := word14 * word3
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := MachineState.readWord s.memory 96
  let v9 : UInt256 := UInt256.mulMod v8 v8 word10
  let v10 : UInt256 := v9 + word2
  let v11 : UInt256 := MachineState.readWord s.memory 192
  let v12 : UInt256 := UInt256.mulMod word11 v11 word10
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := MachineState.readWord s.memory 0
  let v15 : UInt256 := UInt256.mulMod word9 v14 word10
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := MachineState.readWord s.memory 224
  let v18 : UInt256 := UInt256.mulMod v17 word4 word10
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := UInt256.mulMod word7 word8 word10
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.mulMod word6 word5 word10
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := UInt256.mulMod word12 word15 word10
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.mulMod word14 word3 word10
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := UInt256.lnot v7
  let v29 : UInt256 := UInt256.addMod v27 v28 word10
  let v30 : UInt256 := UInt256.shiftRight v29 (UInt256.ofNat 5)
  let v31 : UInt256 := UInt256.land word13 v7
  let v32 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v31.toNat 32) 800
  let v33 : UInt256 := UInt256.shiftLeft v30 (UInt256.ofNat 16)
  let v34 : UInt256 := UInt256.shiftRight v7 (UInt256.ofNat 240)
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := MachineState.readWord v32 32
  let v37 : UInt256 := word16 * v36
  let v38 : UInt256 := MachineState.readWord v32 160
  let v39 : UInt256 := MachineState.readWord v32 64
  let v40 : UInt256 := v39 * v38
  let v41 : UInt256 := v40 + v37
  let v42 : UInt256 := MachineState.readWord v32 128
  let v43 : UInt256 := MachineState.readWord v32 96
  let v44 : UInt256 := v43 * v42
  let v45 : UInt256 := v44 + v41
  let v46 : UInt256 := v45 + v45
  let v47 : UInt256 := UInt256.mulMod word16 v36 word10
  let v48 : UInt256 := MachineState.readWord v32 160
  let v49 : UInt256 := MachineState.readWord v32 64
  let v50 : UInt256 := UInt256.mulMod v49 v48 word10
  let v51 : UInt256 := v50 + v47
  let v52 : UInt256 := MachineState.readWord v32 128
  let v53 : UInt256 := MachineState.readWord v32 96
  {s with pc := UInt256.ofNat 7563, memory := v32, stack := v53 :: v52 :: word10 :: v51 :: v46 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest}

theorem squareColumn10_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10Program {s with pc := UInt256.ofNat 7434, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} =
      some (squareColumn10Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 rest) := by
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := word6 * word5
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := word15 * word12
  let v5 : UInt256 := v4 + v3
  let v6 : UInt256 := word14 * word3
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := MachineState.readWord s.memory 96
  let v9 : UInt256 := UInt256.mulMod v8 v8 word10
  let v10 : UInt256 := v9 + word2
  let v11 : UInt256 := MachineState.readWord s.memory 192
  let v12 : UInt256 := UInt256.mulMod word11 v11 word10
  let v13 : UInt256 := v12 + v10
  let v14 : UInt256 := MachineState.readWord s.memory 0
  let v15 : UInt256 := UInt256.mulMod word9 v14 word10
  let v16 : UInt256 := v15 + v13
  let v17 : UInt256 := MachineState.readWord s.memory 224
  let v18 : UInt256 := UInt256.mulMod v17 word4 word10
  let v19 : UInt256 := v18 + v16
  let v20 : UInt256 := UInt256.mulMod word7 word8 word10
  let v21 : UInt256 := v20 + v19
  let v22 : UInt256 := UInt256.mulMod word6 word5 word10
  let v23 : UInt256 := v22 + v21
  let v24 : UInt256 := UInt256.mulMod word12 word15 word10
  let v25 : UInt256 := v24 + v23
  let v26 : UInt256 := UInt256.mulMod word14 word3 word10
  let v27 : UInt256 := v26 + v25
  let v28 : UInt256 := UInt256.lnot v7
  let v29 : UInt256 := UInt256.addMod v27 v28 word10
  let v30 : UInt256 := UInt256.shiftRight v29 (UInt256.ofNat 5)
  let v31 : UInt256 := UInt256.land word13 v7
  let v32 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v31.toNat 32) 800
  let v33 : UInt256 := UInt256.shiftLeft v30 (UInt256.ofNat 16)
  let v34 : UInt256 := UInt256.shiftRight v7 (UInt256.ofNat 240)
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := MachineState.readWord v32 32
  let v37 : UInt256 := word16 * v36
  let v38 : UInt256 := MachineState.readWord v32 160
  let v39 : UInt256 := MachineState.readWord v32 64
  let v40 : UInt256 := v39 * v38
  let v41 : UInt256 := v40 + v37
  let v42 : UInt256 := MachineState.readWord v32 128
  let v43 : UInt256 := MachineState.readWord v32 96
  let v44 : UInt256 := v43 * v42
  let v45 : UInt256 := v44 + v41
  let v46 : UInt256 := v45 + v45
  let v47 : UInt256 := UInt256.mulMod word16 v36 word10
  let v48 : UInt256 := MachineState.readWord v32 160
  let v49 : UInt256 := MachineState.readWord v32 64
  let v50 : UInt256 := UInt256.mulMod v49 v48 word10
  let v51 : UInt256 := v50 + v47
  let v52 : UInt256 := MachineState.readWord v32 128
  let v53 : UInt256 := MachineState.readWord v32 96
  have h0 : runInstructions squareColumn10part0Program {s with pc := UInt256.ofNat 7434, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7442, memory := s.memory, stack := word15 :: word12 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part0Model, v0, v1, v2, v3] using squareColumn10part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h1 : runInstructions squareColumn10part1Program {s with pc := UInt256.ofNat 7442, memory := s.memory, stack := word15 :: word12 :: v3 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7450, memory := s.memory, stack := word10 :: word2 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part1Model, v4, v5, v6, v7] using squareColumn10part1_run (s) (word15) (word12) (v3) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h2 : runInstructions squareColumn10part2Program {s with pc := UInt256.ofNat 7450, memory := s.memory, stack := word10 :: word2 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7460, memory := s.memory, stack := v11 :: word10 :: v10 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part2Model, v8, v9, v10, v11] using squareColumn10part2_run (s) (word10) (word2) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h3 : runInstructions squareColumn10part3Program {s with pc := UInt256.ofNat 7460, memory := s.memory, stack := v11 :: word10 :: v10 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7468, memory := s.memory, stack := v15 :: v13 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part3Model, v12, v13, v14, v15] using squareColumn10part3_run (s) (v11) (word10) (v10) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h4 : runInstructions squareColumn10part4Program {s with pc := UInt256.ofNat 7468, memory := s.memory, stack := v15 :: v13 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7477, memory := s.memory, stack := word10 :: v19 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part4Model, v16, v17, v18, v19] using squareColumn10part4_run (s) (v15) (v13) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h5 : runInstructions squareColumn10part5Program {s with pc := UInt256.ofNat 7477, memory := s.memory, stack := word10 :: v19 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7485, memory := s.memory, stack := v22 :: v21 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part5Model, v20, v21, v22] using squareColumn10part5_run (s) (word10) (v19) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h6 : runInstructions squareColumn10part6Program {s with pc := UInt256.ofNat 7485, memory := s.memory, stack := v22 :: v21 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7493, memory := s.memory, stack := word3 :: word10 :: v25 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part6Model, v23, v24, v25] using squareColumn10part6_run (s) (v22) (v21) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h7 : runInstructions squareColumn10part7Program {s with pc := UInt256.ofNat 7493, memory := s.memory, stack := word3 :: word10 :: v25 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7501, memory := s.memory, stack := v29 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part7Model, v26, v27, v28, v29] using squareColumn10part7_run (s) (word3) (word10) (v25) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h8 : runInstructions squareColumn10part8Program {s with pc := UInt256.ofNat 7501, memory := s.memory, stack := v29 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7513, memory := v32, stack := (UInt256.ofNat 16) :: v30 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part8Model, v30, v31, v32] using squareColumn10part8_run (s) (v29) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h9 : runInstructions squareColumn10part9Program {s with pc := UInt256.ofNat 7513, memory := v32, stack := (UInt256.ofNat 16) :: v30 :: v7 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7524, memory := v32, stack := v36 :: word10 :: word16 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part9Model, v33, v34, v35, v36] using squareColumn10part9_run ({s with memory := v32}) ((UInt256.ofNat 16)) (v30) (v7) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h10 : runInstructions squareColumn10part10Program {s with pc := UInt256.ofNat 7524, memory := v32, stack := v36 :: word10 :: word16 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7534, memory := v32, stack := v40 :: v37 :: v36 :: word10 :: word16 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part10Model, v37, v38, v39, v40] using squareColumn10part10_run ({s with memory := v32}) (v36) (word10) (word16) (v35) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h11 : runInstructions squareColumn10part11Program {s with pc := UInt256.ofNat 7534, memory := v32, stack := v40 :: v37 :: v36 :: word10 :: word16 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7544, memory := v32, stack := v45 :: v45 :: v36 :: word10 :: word16 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part11Model, v41, v42, v43, v44, v45] using squareColumn10part11_run ({s with memory := v32}) (v40) (v37) (v36) (word10) (word16) (v35) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h12 : runInstructions squareColumn10part12Program {s with pc := UInt256.ofNat 7544, memory := v32, stack := v45 :: v45 :: v36 :: word10 :: word16 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7554, memory := v32, stack := v49 :: v48 :: word10 :: v47 :: v46 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part12Model, v46, v47, v48, v49] using squareColumn10part12_run ({s with memory := v32}) (v45) (v45) (v36) (word10) (word16) (v35) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  have h13 : runInstructions squareColumn10part13Program {s with pc := UInt256.ofNat 7554, memory := v32, stack := v49 :: v48 :: word10 :: v47 :: v46 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} = some {s with pc := UInt256.ofNat 7563, memory := v32, stack := v53 :: v52 :: word10 :: v51 :: v46 :: v35 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: rest} := by
    simpa only [squareColumn10part13Model, v50, v51, v52, v53] using squareColumn10part13_run ({s with memory := v32}) (v49) (v48) (word10) (v47) (v46) (v35) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution
