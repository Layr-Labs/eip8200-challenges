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

def productColumn18part0Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def productColumn18part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x6 x3 x4
  let v3 : UInt256 := v2 + x5
  {s with pc := UInt256.ofNat 10518, memory := s.memory, stack := x15 :: x10 :: v1 :: v3 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem productColumn18part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part0Program {s with pc := UInt256.ofNat 10510, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (productColumn18part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part0Program, productColumn18part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part1Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩)]

def productColumn18part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := x10 * x13
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 10526, memory := s.memory, stack := x5 :: x15 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part1Program {s with pc := UInt256.ofNat 10518, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part1Program, productColumn18part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part2Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn18part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x2
  let v2 : UInt256 := UInt256.mulMod x12 x7 x11
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 10534, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part2Program {s with pc := UInt256.ofNat 10526, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part2Program, productColumn18part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part3Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def productColumn18part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x8 x11 x9
  let v1 : UInt256 := v0 + x0
  {s with pc := UInt256.ofNat 10542, memory := s.memory, stack := x3 :: x13 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part3Program {s with pc := UInt256.ofNat 10534, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part3Program, productColumn18part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5]

def productColumn18part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.lnot x4
  let v3 : UInt256 := UInt256.addMod v1 v2 x12
  {s with pc := UInt256.ofNat 10551, memory := s.memory, stack := (UInt256.ofNat 5) :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn18part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part4Program {s with pc := UInt256.ofNat 10542, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn18part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part4Program, productColumn18part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part5Program : List Instr :=
  [.op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 1 96,
   .op .MSTORE,
   .push 1 16,
   .op .SHL]

def productColumn18part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 x0
  let v1 : UInt256 := UInt256.land x13 x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 96
  let v3 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 10561, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn18part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part5Program {s with pc := UInt256.ofNat 10551, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn18part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part5Program, productColumn18part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]


def productColumn18part6Program : List Instr :=
  [.push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD]

def productColumn18part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2048
  let v1 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 240)
  let v2 : UInt256 := v1 + x0
  let v3 : UInt256 := MachineState.readWord s.memory 160
  {s with pc := UInt256.ofNat 10574, memory := s.memory, stack := v3 :: x9 :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part6Program {s with pc := UInt256.ofNat 10561, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part6Program, productColumn18part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160, ha2048, hf2048]


def productColumn18part7Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn18part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 800
  let v1 : UInt256 := x3 * x0
  {s with pc := UInt256.ofNat 10584, memory := s.memory, stack := v1 :: x2 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: v0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part7Program {s with pc := UInt256.ofNat 10574, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha800 : (800 : UInt256).toNat = 800 := rfl
  have hf800 := Monpro.activeWords_fix s 800 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part7Program, productColumn18part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha800, hf800]


def productColumn18part8Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 2016,
   .op .MLOAD]

def productColumn18part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 2016
  {s with pc := UInt256.ofNat 10594, memory := s.memory, stack := v3 :: x6 :: x13 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn18part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part8Program {s with pc := UInt256.ofNat 10584, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn18part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part8Program, productColumn18part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2016, hf2016]


def productColumn18part9Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn18part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 10602, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn18part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part9Program {s with pc := UInt256.ofNat 10594, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn18part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part9Program, productColumn18part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part10Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL]

def productColumn18part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x10 * x11
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := x8 * x13
  {s with pc := UInt256.ofNat 10610, memory := s.memory, stack := v2 :: v1 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part10Program {s with pc := UInt256.ofNat 10602, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part10Program, productColumn18part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part11Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn18part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x11 x12 x10
  let v2 : UInt256 := v1 + x2
  {s with pc := UInt256.ofNat 10618, memory := s.memory, stack := x10 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn18part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part11Program {s with pc := UInt256.ofNat 10610, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn18part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part11Program, productColumn18part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part12Program : List Instr :=
  [.op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩)]

def productColumn18part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x9 x14 x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := UInt256.lnot x2
  {s with pc := UInt256.ofNat 10626, memory := s.memory, stack := v1 :: v2 :: x10 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn18part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part12Program {s with pc := UInt256.ofNat 10618, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn18part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part12Program, productColumn18part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18part13Program : List Instr :=
  [.op .ADDMOD,
   .push 1 5,
   .op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 1 128,
   .op .MSTORE]

def productColumn18part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.addMod x0 x1 x2
  let v1 : UInt256 := UInt256.shiftRight v0 (UInt256.ofNat 5)
  let v2 : UInt256 := UInt256.land x14 x3
  let v3 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v2.toNat 32) 128
  {s with pc := UInt256.ofNat 10636, memory := v3, stack := v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn18part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part13Program {s with pc := UInt256.ofNat 10626, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn18part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn18part13Program, productColumn18part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha128, hf128]


def productColumn18part14Program : List Instr :=
  [.push 1 16]

def productColumn18part14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10638, memory := s.memory, stack := (UInt256.ofNat 16) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn18part14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18part14Program {s with pc := UInt256.ofNat 10636, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn18part14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn18part14Program, productColumn18part14Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn18Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
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
   .push 1 96,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .push 2 800,
   .op .MLOAD,
   .op (.Swap ⟨8, by decide⟩),
   .op .POP,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
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
   .push 1 16]

def productColumn18Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := word14 * word9
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := word12 * word15
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := word7 * word17
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.mulMod word14 word9 word13
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := UInt256.mulMod word12 word15 word13
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word7 word17 word13
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.lnot v9
  let v17 : UInt256 := UInt256.addMod v15 v16 word13
  let v18 : UInt256 := UInt256.shiftRight v17 (UInt256.ofNat 5)
  let v19 : UInt256 := UInt256.land word16 v9
  let v20 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v19.toNat 32) 96
  let v21 : UInt256 := UInt256.shiftLeft v18 (UInt256.ofNat 16)
  let v22 : UInt256 := MachineState.readWord v20 2048
  let v23 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 240)
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord v20 160
  let v26 : UInt256 := MachineState.readWord v20 800
  let v27 : UInt256 := v22 * v25
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := UInt256.mulMod v22 v25 word13
  let v30 : UInt256 := v29 + v24
  let v31 : UInt256 := MachineState.readWord v20 2016
  let v32 : UInt256 := v31 * word6
  let v33 : UInt256 := v32 + v28
  let v34 : UInt256 := UInt256.mulMod v31 word6 word13
  let v35 : UInt256 := v34 + v30
  let v36 : UInt256 := word14 * word15
  let v37 : UInt256 := v36 + v33
  let v38 : UInt256 := word12 * word17
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.mulMod word14 word15 word13
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := UInt256.mulMod word12 word17 word13
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := UInt256.lnot v39
  let v45 : UInt256 := UInt256.addMod v43 v44 word13
  let v46 : UInt256 := UInt256.shiftRight v45 (UInt256.ofNat 5)
  let v47 : UInt256 := UInt256.land word16 v39
  let v48 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v47.toNat 32) 128
  {s with pc := UInt256.ofNat 10638, memory := v48, stack := (UInt256.ofNat 16) :: v46 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest}

theorem productColumn18_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn18Program {s with pc := UInt256.ofNat 10510, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} =
      some (productColumn18Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 word18 word19 rest) := by
  let v0 : UInt256 := carry * word0
  let v1 : UInt256 := v0 + word1
  let v2 : UInt256 := UInt256.mulMod word5 word2 word3
  let v3 : UInt256 := v2 + word4
  let v4 : UInt256 := word14 * word9
  let v5 : UInt256 := v4 + v1
  let v6 : UInt256 := word12 * word15
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := word7 * word17
  let v9 : UInt256 := v8 + v7
  let v10 : UInt256 := UInt256.mulMod word14 word9 word13
  let v11 : UInt256 := v10 + v3
  let v12 : UInt256 := UInt256.mulMod word12 word15 word13
  let v13 : UInt256 := v12 + v11
  let v14 : UInt256 := UInt256.mulMod word7 word17 word13
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := UInt256.lnot v9
  let v17 : UInt256 := UInt256.addMod v15 v16 word13
  let v18 : UInt256 := UInt256.shiftRight v17 (UInt256.ofNat 5)
  let v19 : UInt256 := UInt256.land word16 v9
  let v20 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v19.toNat 32) 96
  let v21 : UInt256 := UInt256.shiftLeft v18 (UInt256.ofNat 16)
  let v22 : UInt256 := MachineState.readWord v20 2048
  let v23 : UInt256 := UInt256.shiftRight v9 (UInt256.ofNat 240)
  let v24 : UInt256 := v23 + v21
  let v25 : UInt256 := MachineState.readWord v20 160
  let v26 : UInt256 := MachineState.readWord v20 800
  let v27 : UInt256 := v22 * v25
  let v28 : UInt256 := v27 + v24
  let v29 : UInt256 := UInt256.mulMod v22 v25 word13
  let v30 : UInt256 := v29 + v24
  let v31 : UInt256 := MachineState.readWord v20 2016
  let v32 : UInt256 := v31 * word6
  let v33 : UInt256 := v32 + v28
  let v34 : UInt256 := UInt256.mulMod v31 word6 word13
  let v35 : UInt256 := v34 + v30
  let v36 : UInt256 := word14 * word15
  let v37 : UInt256 := v36 + v33
  let v38 : UInt256 := word12 * word17
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.mulMod word14 word15 word13
  let v41 : UInt256 := v40 + v35
  let v42 : UInt256 := UInt256.mulMod word12 word17 word13
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := UInt256.lnot v39
  let v45 : UInt256 := UInt256.addMod v43 v44 word13
  let v46 : UInt256 := UInt256.shiftRight v45 (UInt256.ofNat 5)
  let v47 : UInt256 := UInt256.land word16 v39
  let v48 : ByteArray := MachineState.writeBytes v20 (Data.Bytes.natToBytesPadded v47.toNat 32) 128
  have h0 : runInstructions productColumn18part0Program {s with pc := UInt256.ofNat 10510, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10518, memory := s.memory, stack := word14 :: word9 :: v1 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part0Model, v0, v1, v2, v3] using productColumn18part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h1 : runInstructions productColumn18part1Program {s with pc := UInt256.ofNat 10518, memory := s.memory, stack := word14 :: word9 :: v1 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10526, memory := s.memory, stack := word7 :: word17 :: v7 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part1Model, v4, v5, v6, v7] using productColumn18part1_run (s) (word14) (word9) (v1) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h2 : runInstructions productColumn18part2Program {s with pc := UInt256.ofNat 10526, memory := s.memory, stack := word7 :: word17 :: v7 :: v3 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10534, memory := s.memory, stack := v11 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part2Model, v8, v9, v10, v11] using productColumn18part2_run (s) (word7) (word17) (v7) (v3) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h3 : runInstructions productColumn18part3Program {s with pc := UInt256.ofNat 10534, memory := s.memory, stack := v11 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10542, memory := s.memory, stack := word7 :: word17 :: word13 :: v13 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part3Model, v12, v13] using productColumn18part3_run (s) (v11) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h4 : runInstructions productColumn18part4Program {s with pc := UInt256.ofNat 10542, memory := s.memory, stack := word7 :: word17 :: word13 :: v13 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10551, memory := s.memory, stack := (UInt256.ofNat 5) :: v17 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part4Model, v14, v15, v16, v17] using productColumn18part4_run (s) (word7) (word17) (word13) (v13) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h5 : runInstructions productColumn18part5Program {s with pc := UInt256.ofNat 10551, memory := s.memory, stack := (UInt256.ofNat 5) :: v17 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10561, memory := v20, stack := v21 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part5Model, v18, v19, v20, v21] using productColumn18part5_run (s) ((UInt256.ofNat 5)) (v17) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h6 : runInstructions productColumn18part6Program {s with pc := UInt256.ofNat 10561, memory := v20, stack := v21 :: v9 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10574, memory := v20, stack := v25 :: word13 :: v24 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part6Model, v22, v23, v24, v25] using productColumn18part6_run ({s with memory := v20}) (v21) (v9) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h7 : runInstructions productColumn18part7Program {s with pc := UInt256.ofNat 10574, memory := v20, stack := v25 :: word13 :: v24 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10584, memory := v20, stack := v27 :: v24 :: v25 :: word13 :: v24 :: v22 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part7Model, v26, v27] using productColumn18part7_run ({s with memory := v20}) (v25) (word13) (v24) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h8 : runInstructions productColumn18part8Program {s with pc := UInt256.ofNat 10584, memory := v20, stack := v27 :: v24 :: v25 :: word13 :: v24 :: v22 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10594, memory := v20, stack := v31 :: word6 :: word13 :: v30 :: v28 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part8Model, v28, v29, v30, v31] using productColumn18part8_run ({s with memory := v20}) (v27) (v24) (v25) (word13) (v24) (v22) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h9 : runInstructions productColumn18part9Program {s with pc := UInt256.ofNat 10594, memory := v20, stack := v31 :: word6 :: word13 :: v30 :: v28 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10602, memory := v20, stack := v35 :: v33 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part9Model, v32, v33, v34, v35] using productColumn18part9_run ({s with memory := v20}) (v31) (word6) (word13) (v30) (v28) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h10 : runInstructions productColumn18part10Program {s with pc := UInt256.ofNat 10602, memory := v20, stack := v35 :: v33 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10610, memory := v20, stack := v38 :: v37 :: v35 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part10Model, v36, v37, v38] using productColumn18part10_run ({s with memory := v20}) (v35) (v33) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h11 : runInstructions productColumn18part11Program {s with pc := UInt256.ofNat 10610, memory := v20, stack := v38 :: v37 :: v35 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10618, memory := v20, stack := word13 :: v41 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part11Model, v39, v40, v41] using productColumn18part11_run ({s with memory := v20}) (v38) (v37) (v35) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h12 : runInstructions productColumn18part12Program {s with pc := UInt256.ofNat 10618, memory := v20, stack := word13 :: v41 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10626, memory := v20, stack := v43 :: v44 :: word13 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part12Model, v42, v43, v44] using productColumn18part12_run ({s with memory := v20}) (word13) (v41) (v39) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h13 : runInstructions productColumn18part13Program {s with pc := UInt256.ofNat 10626, memory := v20, stack := v43 :: v44 :: word13 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10636, memory := v48, stack := v46 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part13Model, v45, v46, v47, v48] using productColumn18part13_run ({s with memory := v20}) (v43) (v44) (word13) (v39) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  have h14 : runInstructions productColumn18part14Program {s with pc := UInt256.ofNat 10636, memory := v48, stack := v46 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} = some {s with pc := UInt256.ofNat 10638, memory := v48, stack := (UInt256.ofNat 16) :: v46 :: v39 :: word6 :: word7 :: word8 :: v26 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: word18 :: word19 :: rest} := by
    simpa only [productColumn18part14Model] using productColumn18part14_run ({s with memory := v48}) (v46) (v39) (word6) (word7) (word8) (v26) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) (word18) (word19) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 h14))))))))))))))


end CycleSubmission.Execution
