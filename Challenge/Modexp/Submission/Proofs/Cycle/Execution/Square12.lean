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

def squareColumn12part0Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def squareColumn12part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := x11 * v2
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 7702, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn12part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part0Program {s with pc := UInt256.ofNat 7693, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn12part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part0Program, squareColumn12part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def squareColumn12part1Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MUL,
   .op .ADD]

def squareColumn12part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x8 * x6
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x5 * x3
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7710, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part1Program {s with pc := UInt256.ofNat 7702, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part1Program, squareColumn12part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part2Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .MUL,
   .op .ADD]

def squareColumn12part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x7 * x11
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x13 * x4
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7718, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part2Program {s with pc := UInt256.ofNat 7710, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part2Program, squareColumn12part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part3Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn12part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := UInt256.mulMod v0 v0 x9
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 7727, memory := s.memory, stack := x9 :: v2 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part3Program {s with pc := UInt256.ofNat 7718, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part3Program, squareColumn12part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def squareColumn12part4Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨10, by decide⟩)]

def squareColumn12part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.mulMod x11 v0 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 7736, memory := s.memory, stack := x9 :: x7 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn12part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part4Program {s with pc := UInt256.ofNat 7727, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn12part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part4Program, squareColumn12part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def squareColumn12part5Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn12part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x8 x6 x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7744, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn12part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part5Program {s with pc := UInt256.ofNat 7736, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn12part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part5Program, squareColumn12part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part6Program : List Instr :=
  [.op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MULMOD]

def squareColumn12part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x12 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.mulMod x14 x5 x10
  {s with pc := UInt256.ofNat 7752, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn12part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part6Program {s with pc := UInt256.ofNat 7744, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn12part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part6Program, squareColumn12part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part7Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR]

def squareColumn12part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.lnot x2
  let v2 : UInt256 := UInt256.addMod v0 v1 x10
  let v3 : UInt256 := UInt256.shiftRight v2 (UInt256.ofNat 5)
  {s with pc := UInt256.ofNat 7761, memory := s.memory, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn12part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part7Program {s with pc := UInt256.ofNat 7752, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn12part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part7Program, squareColumn12part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part8Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 1 32,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩)]

def squareColumn12part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.land x12 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 32
  let v2 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 7771, memory := v1, stack := x1 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part8Program {s with pc := UInt256.ofNat 7761, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part8Program, squareColumn12part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32]


def squareColumn12part9Program : List Instr :=
  [.push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn12part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x0 (UInt256.ofNat 240)
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 96
  {s with pc := UInt256.ofNat 7781, memory := s.memory, stack := v2 :: v2 :: x9 :: x15 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part9Program {s with pc := UInt256.ofNat 7771, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part9Program, squareColumn12part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]


def squareColumn12part10Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 128,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def squareColumn12part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x0
  let v1 : UInt256 := MachineState.readWord s.memory 160
  let v2 : UInt256 := MachineState.readWord s.memory 128
  let v3 : UInt256 := v2 * v1
  let v4 : UInt256 := v3 + v0
  {s with pc := UInt256.ofNat 7791, memory := s.memory, stack := v4 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn12part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part10Program {s with pc := UInt256.ofNat 7781, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn12part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part10Program, squareColumn12part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha160, hf160]


def squareColumn12part11Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 128,
   .op .MLOAD]

def squareColumn12part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := UInt256.mulMod x3 x1 x2
  let v2 : UInt256 := MachineState.readWord s.memory 160
  let v3 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 7802, memory := s.memory, stack := v3 :: v2 :: x12 :: v1 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn12part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part11Program {s with pc := UInt256.ofNat 7791, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn12part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn12part11Program, squareColumn12part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128, ha160, hf160]


def squareColumn12part12Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD]

def squareColumn12part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := x5 + v2
  let v4 : UInt256 := x5 + x4
  {s with pc := UInt256.ofNat 7810, memory := s.memory, stack := v4 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn12part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part12Program {s with pc := UInt256.ofNat 7802, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn12part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part12Program, squareColumn12part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part13Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD]

def squareColumn12part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x10 * x6
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := x8 * x5
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 7818, memory := s.memory, stack := v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part13Program {s with pc := UInt256.ofNat 7810, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part13Program, squareColumn12part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12part14Program : List Instr :=
  [.op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL]

def squareColumn12part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x3 * x11
  {s with pc := UInt256.ofNat 7821, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn12part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12part14Program {s with pc := UInt256.ofNat 7818, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn12part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn12part14Program, squareColumn12part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn12Program : List Instr :=
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
   .push 1 32,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
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

def squareColumn12Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := word10 * v2
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := word8 * word6
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := word5 * word3
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := word7 * word11
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := word13 * word4
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := MachineState.readWord s.memory 128
  let v14 : UInt256 := UInt256.mulMod v13 v13 word9
  let v15 : UInt256 := v14 + word1
  let v16 : UInt256 := MachineState.readWord s.memory 224
  let v17 : UInt256 := UInt256.mulMod word10 v16 word9
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := UInt256.mulMod word8 word6 word9
  let v20 : UInt256 := v19 + v18
  let v21 : UInt256 := UInt256.mulMod word5 word3 word9
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := UInt256.mulMod word7 word11 word9
  let v24 : UInt256 := v23 + v22
  let v25 : UInt256 := UInt256.mulMod word13 word4 word9
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := UInt256.lnot v12
  let v28 : UInt256 := UInt256.addMod v26 v27 word9
  let v29 : UInt256 := UInt256.shiftRight v28 (UInt256.ofNat 5)
  let v30 : UInt256 := UInt256.land word12 v12
  let v31 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v30.toNat 32) 32
  let v32 : UInt256 := UInt256.shiftLeft v29 (UInt256.ofNat 16)
  let v33 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 240)
  let v34 : UInt256 := v33 + v32
  let v35 : UInt256 := MachineState.readWord v31 96
  let v36 : UInt256 := word15 * v35
  let v37 : UInt256 := MachineState.readWord v31 160
  let v38 : UInt256 := MachineState.readWord v31 128
  let v39 : UInt256 := v38 * v37
  let v40 : UInt256 := v39 + v36
  let v41 : UInt256 := v40 + v40
  let v42 : UInt256 := UInt256.mulMod word15 v35 word9
  let v43 : UInt256 := MachineState.readWord v31 160
  let v44 : UInt256 := MachineState.readWord v31 128
  let v45 : UInt256 := UInt256.mulMod v44 v43 word9
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := v46 + v46
  let v48 : UInt256 := v34 + v47
  let v49 : UInt256 := v34 + v41
  let v50 : UInt256 := word10 * word6
  let v51 : UInt256 := v50 + v49
  let v52 : UInt256 := word8 * word5
  let v53 : UInt256 := v52 + v51
  let v54 : UInt256 := word3 * word11
  {s with pc := UInt256.ofNat 7821, memory := v31, stack := v54 :: v53 :: v48 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest}

theorem squareColumn12_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn12Program {s with pc := UInt256.ofNat 7693, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} =
      some (squareColumn12Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 rest) := by
  let v0 : UInt256 := carry * carry
  let v1 : UInt256 := v0 + word0
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := word10 * v2
  let v4 : UInt256 := v3 + v1
  let v5 : UInt256 := word8 * word6
  let v6 : UInt256 := v5 + v4
  let v7 : UInt256 := word5 * word3
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := word7 * word11
  let v10 : UInt256 := v9 + v8
  let v11 : UInt256 := word13 * word4
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := MachineState.readWord s.memory 128
  let v14 : UInt256 := UInt256.mulMod v13 v13 word9
  let v15 : UInt256 := v14 + word1
  let v16 : UInt256 := MachineState.readWord s.memory 224
  let v17 : UInt256 := UInt256.mulMod word10 v16 word9
  let v18 : UInt256 := v17 + v15
  let v19 : UInt256 := UInt256.mulMod word8 word6 word9
  let v20 : UInt256 := v19 + v18
  let v21 : UInt256 := UInt256.mulMod word5 word3 word9
  let v22 : UInt256 := v21 + v20
  let v23 : UInt256 := UInt256.mulMod word7 word11 word9
  let v24 : UInt256 := v23 + v22
  let v25 : UInt256 := UInt256.mulMod word13 word4 word9
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := UInt256.lnot v12
  let v28 : UInt256 := UInt256.addMod v26 v27 word9
  let v29 : UInt256 := UInt256.shiftRight v28 (UInt256.ofNat 5)
  let v30 : UInt256 := UInt256.land word12 v12
  let v31 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v30.toNat 32) 32
  let v32 : UInt256 := UInt256.shiftLeft v29 (UInt256.ofNat 16)
  let v33 : UInt256 := UInt256.shiftRight v12 (UInt256.ofNat 240)
  let v34 : UInt256 := v33 + v32
  let v35 : UInt256 := MachineState.readWord v31 96
  let v36 : UInt256 := word15 * v35
  let v37 : UInt256 := MachineState.readWord v31 160
  let v38 : UInt256 := MachineState.readWord v31 128
  let v39 : UInt256 := v38 * v37
  let v40 : UInt256 := v39 + v36
  let v41 : UInt256 := v40 + v40
  let v42 : UInt256 := UInt256.mulMod word15 v35 word9
  let v43 : UInt256 := MachineState.readWord v31 160
  let v44 : UInt256 := MachineState.readWord v31 128
  let v45 : UInt256 := UInt256.mulMod v44 v43 word9
  let v46 : UInt256 := v45 + v42
  let v47 : UInt256 := v46 + v46
  let v48 : UInt256 := v34 + v47
  let v49 : UInt256 := v34 + v41
  let v50 : UInt256 := word10 * word6
  let v51 : UInt256 := v50 + v49
  let v52 : UInt256 := word8 * word5
  let v53 : UInt256 := v52 + v51
  let v54 : UInt256 := word3 * word11
  have h0 : runInstructions squareColumn12part0Program {s with pc := UInt256.ofNat 7693, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7702, memory := s.memory, stack := v4 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part0Model, v0, v1, v2, v3, v4] using squareColumn12part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h1 : runInstructions squareColumn12part1Program {s with pc := UInt256.ofNat 7702, memory := s.memory, stack := v4 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7710, memory := s.memory, stack := v8 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part1Model, v5, v6, v7, v8] using squareColumn12part1_run (s) (v4) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h2 : runInstructions squareColumn12part2Program {s with pc := UInt256.ofNat 7710, memory := s.memory, stack := v8 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7718, memory := s.memory, stack := v12 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part2Model, v9, v10, v11, v12] using squareColumn12part2_run (s) (v8) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h3 : runInstructions squareColumn12part3Program {s with pc := UInt256.ofNat 7718, memory := s.memory, stack := v12 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7727, memory := s.memory, stack := word9 :: v15 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part3Model, v13, v14, v15] using squareColumn12part3_run (s) (v12) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h4 : runInstructions squareColumn12part4Program {s with pc := UInt256.ofNat 7727, memory := s.memory, stack := word9 :: v15 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7736, memory := s.memory, stack := word8 :: word6 :: word9 :: v18 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part4Model, v16, v17, v18] using squareColumn12part4_run (s) (word9) (v15) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h5 : runInstructions squareColumn12part5Program {s with pc := UInt256.ofNat 7736, memory := s.memory, stack := word8 :: word6 :: word9 :: v18 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7744, memory := s.memory, stack := word9 :: v22 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part5Model, v19, v20, v21, v22] using squareColumn12part5_run (s) (word8) (word6) (word9) (v18) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h6 : runInstructions squareColumn12part6Program {s with pc := UInt256.ofNat 7744, memory := s.memory, stack := word9 :: v22 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7752, memory := s.memory, stack := v25 :: v24 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part6Model, v23, v24, v25] using squareColumn12part6_run (s) (word9) (v22) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h7 : runInstructions squareColumn12part7Program {s with pc := UInt256.ofNat 7752, memory := s.memory, stack := v25 :: v24 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7761, memory := s.memory, stack := v29 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part7Model, v26, v27, v28, v29] using squareColumn12part7_run (s) (v25) (v24) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h8 : runInstructions squareColumn12part8Program {s with pc := UInt256.ofNat 7761, memory := s.memory, stack := v29 :: v12 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7771, memory := v31, stack := v12 :: v32 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part8Model, v30, v31, v32] using squareColumn12part8_run (s) (v29) (v12) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h9 : runInstructions squareColumn12part9Program {s with pc := UInt256.ofNat 7771, memory := v31, stack := v12 :: v32 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7781, memory := v31, stack := v35 :: v35 :: word9 :: word15 :: v34 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part9Model, v33, v34, v35] using squareColumn12part9_run ({s with memory := v31}) (v12) (v32) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h10 : runInstructions squareColumn12part10Program {s with pc := UInt256.ofNat 7781, memory := v31, stack := v35 :: v35 :: word9 :: word15 :: v34 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7791, memory := v31, stack := v40 :: v35 :: word9 :: word15 :: v34 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part10Model, v36, v37, v38, v39, v40] using squareColumn12part10_run ({s with memory := v31}) (v35) (v35) (word9) (word15) (v34) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h11 : runInstructions squareColumn12part11Program {s with pc := UInt256.ofNat 7791, memory := v31, stack := v40 :: v35 :: word9 :: word15 :: v34 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7802, memory := v31, stack := v44 :: v43 :: word9 :: v42 :: v41 :: v34 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part11Model, v41, v42, v43, v44] using squareColumn12part11_run ({s with memory := v31}) (v40) (v35) (word9) (word15) (v34) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h12 : runInstructions squareColumn12part12Program {s with pc := UInt256.ofNat 7802, memory := v31, stack := v44 :: v43 :: word9 :: v42 :: v41 :: v34 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7810, memory := v31, stack := v49 :: v48 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part12Model, v45, v46, v47, v48, v49] using squareColumn12part12_run ({s with memory := v31}) (v44) (v43) (word9) (v42) (v41) (v34) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h13 : runInstructions squareColumn12part13Program {s with pc := UInt256.ofNat 7810, memory := v31, stack := v49 :: v48 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7818, memory := v31, stack := v53 :: v48 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part13Model, v50, v51, v52, v53] using squareColumn12part13_run ({s with memory := v31}) (v49) (v48) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h14 : runInstructions squareColumn12part14Program {s with pc := UInt256.ofNat 7818, memory := v31, stack := v53 :: v48 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7821, memory := v31, stack := v54 :: v53 :: v48 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn12part14Model, v54] using squareColumn12part14_run ({s with memory := v31}) (v53) (v48) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))


end CycleSubmission.Execution
