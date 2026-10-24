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

def squareColumn14part0Program : List Instr :=
  [.op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩)]

def squareColumn14part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x1 x0
  let v1 : UInt256 := UInt256.shiftRight x2 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 800
  {s with pc := UInt256.ofNat 7961, memory := s.memory, stack := x6 :: v2 :: x3 :: x4 :: x5 :: v3 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part0Program {s with pc := UInt256.ofNat 7950, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part0Program, squareColumn14part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha800, hf800]


def squareColumn14part1Program : List Instr :=
  [.op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def squareColumn14part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := x15 * v0
  {s with pc := UInt256.ofNat 7970, memory := s.memory, stack := v1 :: v0 :: x9 :: x15 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn14part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part1Program {s with pc := UInt256.ofNat 7961, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn14part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part1Program, squareColumn14part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def squareColumn14part2Program : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD]

def squareColumn14part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x0
  let v1 : UInt256 := UInt256.mulMod x3 x1 x2
  let v2 : UInt256 := v1 + v1
  let v3 : UInt256 := x4 + v2
  {s with pc := UInt256.ofNat 7978, memory := s.memory, stack := v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn14part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part2Program {s with pc := UInt256.ofNat 7970, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn14part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part2Program, squareColumn14part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part3Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn14part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 + x1
  let v1 : UInt256 := x11 * x12
  let v2 : UInt256 := v1 + v0
  {s with pc := UInt256.ofNat 7986, memory := s.memory, stack := x9 :: x14 :: v2 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part3Program {s with pc := UInt256.ofNat 7978, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part3Program, squareColumn14part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part4Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def squareColumn14part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x12 x13 x11
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 7994, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part4Program {s with pc := UInt256.ofNat 7986, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part4Program, squareColumn14part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part5Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩)]

def squareColumn14part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x13 x9
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.lnot x1
  {s with pc := UInt256.ofNat 8002, memory := s.memory, stack := x9 :: v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn14part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part5Program {s with pc := UInt256.ofNat 7994, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn14part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part5Program, squareColumn14part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part6Program : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 1 128,
   .op .MSTORE]

def squareColumn14part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.addMod x2 x1 x0
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := UInt256.land x14 x3
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 128
  {s with pc := UInt256.ofNat 8013, memory := v3, stack := v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part6Program {s with pc := UInt256.ofNat 8002, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part6Program, squareColumn14part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def squareColumn14part7Program : List Instr :=
  [.push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .push 2 1376,
   .op .MLOAD]

def squareColumn14part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft x0 (UInt256.ofNat 16)
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 1376
  {s with pc := UInt256.ofNat 8025, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn14part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part7Program {s with pc := UInt256.ofNat 8013, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn14part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  have ha1376 : (1376 : UInt256).toNat = 1376 := rfl
  have hf1376 := Monpro.activeWords_fix s 1376 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part7Program, squareColumn14part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1376, hf1376]


def squareColumn14part8Program : List Instr :=
  [.op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩)]

def squareColumn14part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x15 x15 x9
  {s with pc := UInt256.ofNat 8033, memory := s.memory, stack := x15 :: x15 :: v0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x0 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn14part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part8Program {s with pc := UInt256.ofNat 8025, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn14part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part8Program, squareColumn14part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part9Program : List Instr :=
  [.op .MUL,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩)]

def squareColumn14part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := x3 + v0
  let v2 : UInt256 := x15 * x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 8041, memory := s.memory, stack := x3 :: x2 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn14part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part9Program {s with pc := UInt256.ofNat 8033, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn14part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part9Program, squareColumn14part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part10Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT]

def squareColumn14part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x11 x14 x10
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := UInt256.lnot x2
  {s with pc := UInt256.ofNat 8049, memory := s.memory, stack := v3 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part10Program {s with pc := UInt256.ofNat 8041, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part10Program, squareColumn14part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part11Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND]

def squareColumn14part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.addMod x1 x0 x10
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := UInt256.land x13 x2
  {s with pc := UInt256.ofNat 8058, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part11Program {s with pc := UInt256.ofNat 8049, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn14part11Program, squareColumn14part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn14part12Program : List Instr :=
  [.push 1 160,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD]

def squareColumn14part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 160
  let v1 : UInt256 := UInt256.shiftLeft x1 (UInt256.ofNat 16)
  let v2 : UInt256 := UInt256.shiftRight x2 (UInt256.ofNat 240)
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 8069, memory := v0, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn14part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part12Program {s with pc := UInt256.ofNat 8058, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn14part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part12Program, squareColumn14part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def squareColumn14part13Program : List Instr :=
  [.op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP]

def squareColumn14part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1344
  {s with pc := UInt256.ofNat 8077, memory := s.memory, stack := x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: v0 :: x13 :: x0 :: rest}

theorem squareColumn14part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14part13Program {s with pc := UInt256.ofNat 8069, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (squareColumn14part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 15) : rest.length + j < 1024 := by omega
  have ha1344 : (1344 : UInt256).toNat = 1344 := rfl
  have hf1344 := Monpro.activeWords_fix s 1344 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn14part13Program, squareColumn14part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1344, hf1344]


def squareColumn14Program : List Instr :=
  [.op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .POP,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
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
   .push 1 128,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .push 2 1376,
   .op .MLOAD,
   .op (.Swap ⟨10, by decide⟩),
   .op .POP,
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
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
   .push 1 160,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .push 2 1344,
   .op .MLOAD,
   .op (.Swap ⟨11, by decide⟩),
   .op .POP]

def squareColumn14Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftLeft word0 carry
  let v1 : UInt256 := UInt256.shiftRight word1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 800
  let v4 : UInt256 := MachineState.readWord s.memory 160
  let v5 : UInt256 := word15 * v4
  let v6 : UInt256 := v5 + v5
  let v7 : UInt256 := UInt256.mulMod word15 v4 word9
  let v8 : UInt256 := v7 + v7
  let v9 : UInt256 := v2 + v8
  let v10 : UInt256 := v2 + v6
  let v11 : UInt256 := word10 * word11
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := word8 * word13
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := UInt256.mulMod word10 word11 word9
  let v16 : UInt256 := v15 + v9
  let v17 : UInt256 := UInt256.mulMod word8 word13 word9
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := UInt256.lnot v14
  let v20 : UInt256 := UInt256.addMod v18 v19 word9
  let v21 : UInt256 := UInt256.shiftRight v20 (UInt256.ofNat 5)
  let v22 : UInt256 := UInt256.land word12 v14
  let v23 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v22.toNat 32) 128
  let v24 : UInt256 := UInt256.shiftLeft v21 (UInt256.ofNat 16)
  let v25 : UInt256 := UInt256.shiftRight v14 (UInt256.ofNat 240)
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord v23 1376
  let v28 : UInt256 := UInt256.mulMod word15 word15 word9
  let v29 : UInt256 := word15 * word15
  let v30 : UInt256 := v26 + v29
  let v31 : UInt256 := word13 * word10
  let v32 : UInt256 := v31 + v30
  let v33 : UInt256 := v26 + v28
  let v34 : UInt256 := UInt256.mulMod word10 word13 word9
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := UInt256.lnot v32
  let v37 : UInt256 := UInt256.addMod v35 v36 word9
  let v38 : UInt256 := UInt256.shiftRight v37 (UInt256.ofNat 5)
  let v39 : UInt256 := UInt256.land word12 v32
  let v40 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v39.toNat 32) 160
  let v41 : UInt256 := UInt256.shiftLeft v38 (UInt256.ofNat 16)
  let v42 : UInt256 := UInt256.shiftRight v32 (UInt256.ofNat 240)
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := MachineState.readWord v40 1344
  {s with pc := UInt256.ofNat 8077, memory := v40, stack := word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: v44 :: word14 :: v43 :: rest}

theorem squareColumn14_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14Program {s with pc := UInt256.ofNat 7950, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} =
      some (squareColumn14Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 rest) := by
  let v0 : UInt256 := UInt256.shiftLeft word0 carry
  let v1 : UInt256 := UInt256.shiftRight word1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + v0
  let v3 : UInt256 := MachineState.readWord s.memory 800
  let v4 : UInt256 := MachineState.readWord s.memory 160
  let v5 : UInt256 := word15 * v4
  let v6 : UInt256 := v5 + v5
  let v7 : UInt256 := UInt256.mulMod word15 v4 word9
  let v8 : UInt256 := v7 + v7
  let v9 : UInt256 := v2 + v8
  let v10 : UInt256 := v2 + v6
  let v11 : UInt256 := word10 * word11
  let v12 : UInt256 := v11 + v10
  let v13 : UInt256 := word8 * word13
  let v14 : UInt256 := v13 + v12
  let v15 : UInt256 := UInt256.mulMod word10 word11 word9
  let v16 : UInt256 := v15 + v9
  let v17 : UInt256 := UInt256.mulMod word8 word13 word9
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := UInt256.lnot v14
  let v20 : UInt256 := UInt256.addMod v18 v19 word9
  let v21 : UInt256 := UInt256.shiftRight v20 (UInt256.ofNat 5)
  let v22 : UInt256 := UInt256.land word12 v14
  let v23 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v22.toNat 32) 128
  let v24 : UInt256 := UInt256.shiftLeft v21 (UInt256.ofNat 16)
  let v25 : UInt256 := UInt256.shiftRight v14 (UInt256.ofNat 240)
  let v26 : UInt256 := v25 + v24
  let v27 : UInt256 := MachineState.readWord v23 1376
  let v28 : UInt256 := UInt256.mulMod word15 word15 word9
  let v29 : UInt256 := word15 * word15
  let v30 : UInt256 := v26 + v29
  let v31 : UInt256 := word13 * word10
  let v32 : UInt256 := v31 + v30
  let v33 : UInt256 := v26 + v28
  let v34 : UInt256 := UInt256.mulMod word10 word13 word9
  let v35 : UInt256 := v34 + v33
  let v36 : UInt256 := UInt256.lnot v32
  let v37 : UInt256 := UInt256.addMod v35 v36 word9
  let v38 : UInt256 := UInt256.shiftRight v37 (UInt256.ofNat 5)
  let v39 : UInt256 := UInt256.land word12 v32
  let v40 : ByteArray := MachineState.writeBytes v23 (Data.Bytes.natToBytesPadded v39.toNat 32) 160
  let v41 : UInt256 := UInt256.shiftLeft v38 (UInt256.ofNat 16)
  let v42 : UInt256 := UInt256.shiftRight v32 (UInt256.ofNat 240)
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := MachineState.readWord v40 1344
  have h0 : runInstructions squareColumn14part0Program {s with pc := UInt256.ofNat 7950, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7961, memory := s.memory, stack := word5 :: v2 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part0Model, v0, v1, v2, v3] using squareColumn14part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h1 : runInstructions squareColumn14part1Program {s with pc := UInt256.ofNat 7961, memory := s.memory, stack := word5 :: v2 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7970, memory := s.memory, stack := v5 :: v4 :: word9 :: word15 :: v2 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part1Model, v4, v5] using squareColumn14part1_run (s) (word5) (v2) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h2 : runInstructions squareColumn14part2Program {s with pc := UInt256.ofNat 7970, memory := s.memory, stack := v5 :: v4 :: word9 :: word15 :: v2 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7978, memory := s.memory, stack := v9 :: v6 :: v2 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part2Model, v6, v7, v8, v9] using squareColumn14part2_run (s) (v5) (v4) (word9) (word15) (v2) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h3 : runInstructions squareColumn14part3Program {s with pc := UInt256.ofNat 7978, memory := s.memory, stack := v9 :: v6 :: v2 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7986, memory := s.memory, stack := word8 :: word13 :: v12 :: v9 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part3Model, v10, v11, v12] using squareColumn14part3_run (s) (v9) (v6) (v2) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h4 : runInstructions squareColumn14part4Program {s with pc := UInt256.ofNat 7986, memory := s.memory, stack := word8 :: word13 :: v12 :: v9 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 7994, memory := s.memory, stack := v16 :: v14 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part4Model, v13, v14, v15, v16] using squareColumn14part4_run (s) (word8) (word13) (v12) (v9) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h5 : runInstructions squareColumn14part5Program {s with pc := UInt256.ofNat 7994, memory := s.memory, stack := v16 :: v14 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8002, memory := s.memory, stack := word9 :: v19 :: v18 :: v14 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part5Model, v17, v18, v19] using squareColumn14part5_run (s) (v16) (v14) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h6 : runInstructions squareColumn14part6Program {s with pc := UInt256.ofNat 8002, memory := s.memory, stack := word9 :: v19 :: v18 :: v14 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8013, memory := v23, stack := v21 :: v14 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part6Model, v20, v21, v22, v23] using squareColumn14part6_run (s) (word9) (v19) (v18) (v14) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h7 : runInstructions squareColumn14part7Program {s with pc := UInt256.ofNat 8013, memory := v23, stack := v21 :: v14 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8025, memory := v23, stack := v27 :: v26 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part7Model, v24, v25, v26, v27] using squareColumn14part7_run ({s with memory := v23}) (v21) (v14) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h8 : runInstructions squareColumn14part8Program {s with pc := UInt256.ofNat 8025, memory := v23, stack := v27 :: v26 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8033, memory := v23, stack := word15 :: word15 :: v28 :: v26 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part8Model, v28] using squareColumn14part8_run ({s with memory := v23}) (v27) (v26) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h9 : runInstructions squareColumn14part9Program {s with pc := UInt256.ofNat 8033, memory := v23, stack := word15 :: word15 :: v28 :: v26 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8041, memory := v23, stack := v26 :: v28 :: v32 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part9Model, v29, v30, v31, v32] using squareColumn14part9_run ({s with memory := v23}) (word15) (word15) (v28) (v26) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (v27) (word12) (word13) (word14) (word15) rest hcap hact
  have h10 : runInstructions squareColumn14part10Program {s with pc := UInt256.ofNat 8041, memory := v23, stack := v26 :: v28 :: v32 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8049, memory := v23, stack := v36 :: v35 :: v32 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part10Model, v33, v34, v35, v36] using squareColumn14part10_run ({s with memory := v23}) (v26) (v28) (v32) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (v27) (word12) (word13) (word14) (word15) rest hcap hact
  have h11 : runInstructions squareColumn14part11Program {s with pc := UInt256.ofNat 8049, memory := v23, stack := v36 :: v35 :: v32 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8058, memory := v23, stack := v39 :: v38 :: v32 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part11Model, v37, v38, v39] using squareColumn14part11_run ({s with memory := v23}) (v36) (v35) (v32) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (v27) (word12) (word13) (word14) (word15) rest hcap hact
  have h12 : runInstructions squareColumn14part12Program {s with pc := UInt256.ofNat 8058, memory := v23, stack := v39 :: v38 :: v32 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8069, memory := v40, stack := v43 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [squareColumn14part12Model, v40, v41, v42, v43] using squareColumn14part12_run ({s with memory := v23}) (v39) (v38) (v32) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (v27) (word12) (word13) (word14) (word15) rest hcap hact
  have h13 : runInstructions squareColumn14part13Program {s with pc := UInt256.ofNat 8069, memory := v40, stack := v43 :: word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 8077, memory := v40, stack := word2 :: word3 :: word4 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: v27 :: word12 :: v44 :: word14 :: v43 :: rest} := by
    simpa only [squareColumn14part13Model, v44] using squareColumn14part13_run ({s with memory := v40}) (v43) (word2) (word3) (word4) (v3) (word6) (word7) (word8) (word9) (word10) (v27) (word12) (word13) (word14) (word15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution
