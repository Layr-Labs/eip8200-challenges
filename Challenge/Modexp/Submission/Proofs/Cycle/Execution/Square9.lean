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

def squareColumn9part0Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def squareColumn9part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod x8 x17 x12
  let v3 : UInt256 := v2 + v1
  {s with pc := UInt256.ofNat 6856, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn9part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part0Program {s with pc := UInt256.ofNat 6848, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn9part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn9part0Program, squareColumn9part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn9part1Program : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨15, by decide⟩)]

def squareColumn9part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := UInt256.mulMod v0 x3 x0
  let v2 : UInt256 := v1 + x1
  {s with pc := UInt256.ofNat 6866, memory := s.memory, stack := x14 :: x12 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn9part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part1Program {s with pc := UInt256.ofNat 6856, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn9part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part1Program, squareColumn9part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def squareColumn9part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨1, by decide⟩),
   .op .NOT,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨1, by decide⟩),
   .op .ADDMOD,
   .push 1 5]

def squareColumn9part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.lnot x4
  let v3 : UInt256 := UInt256.addMod v1 v2 x12
  {s with pc := UInt256.ofNat 6875, memory := s.memory, stack := (UInt256.ofNat 5) :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn9part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part2Program {s with pc := UInt256.ofNat 6866, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn9part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn9part2Program, squareColumn9part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn9part3Program : List Instr :=
  [.op .SHR,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push 2 768,
   .op .MSTORE,
   .push 1 16,
   .op .SHL]

def squareColumn9part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 x0
  let v1 : UInt256 := UInt256.land x13 x2
  let v2 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v1.toNat 32) 768
  let v3 : UInt256 := UInt256.shiftLeft v0 (UInt256.ofNat 16)
  {s with pc := UInt256.ofNat 6886, memory := v2, stack := v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn9part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part3Program {s with pc := UInt256.ofNat 6875, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn9part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha768 : (768 : UInt256).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part3Program, squareColumn9part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha768, hf768]


def squareColumn9part4Program : List Instr :=
  [.op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def squareColumn9part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.shiftRight x1 (UInt256.ofNat 240)
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 6897, memory := s.memory, stack := v2 :: x9 :: x15 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn9part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part4Program {s with pc := UInt256.ofNat 6886, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn9part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part4Program, squareColumn9part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1216, hf1216]


def squareColumn9part5Program : List Instr :=
  [.push 2 1280,
   .op .MLOAD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL]

def squareColumn9part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 1280
  let v1 : UInt256 := x2 * x8
  {s with pc := UInt256.ofNat 6907, memory := s.memory, stack := v1 :: x8 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x0 :: x9 :: x10 :: x11 :: x12 :: v0 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn9part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part5Program {s with pc := UInt256.ofNat 6897, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn9part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part5Program, squareColumn9part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def squareColumn9part6Program : List Instr :=
  [.push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD]

def squareColumn9part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := MachineState.readWord s.memory 32
  let v2 : UInt256 := v1 * v0
  let v3 : UInt256 := v2 + x0
  let v4 : UInt256 := MachineState.readWord s.memory 128
  {s with pc := UInt256.ofNat 6918, memory := s.memory, stack := v4 :: v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem squareColumn9part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part6Program {s with pc := UInt256.ofNat 6907, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (squareColumn9part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part6Program, squareColumn9part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha128, hf128, ha160, hf160]


def squareColumn9part7Program : List Instr :=
  [.push 1 64,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MULMOD]

def squareColumn9part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 64
  let v1 : UInt256 := v0 * x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := v2 + v2
  let v4 : UInt256 := UInt256.mulMod x4 x2 x3
  {s with pc := UInt256.ofNat 6927, memory := s.memory, stack := v4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem squareColumn9part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part7Program {s with pc := UInt256.ofNat 6918, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (squareColumn9part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part7Program, squareColumn9part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64]


def squareColumn9part8Program : List Instr :=
  [.op (.Dup ⟨10, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩)]

def squareColumn9part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := MachineState.readWord s.memory 32
  let v2 : UInt256 := UInt256.mulMod v1 v0 x10
  let v3 : UInt256 := v2 + x0
  {s with pc := UInt256.ofNat 6937, memory := s.memory, stack := x10 :: v3 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn9part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part8Program {s with pc := UInt256.ofNat 6927, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn9part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part8Program, squareColumn9part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha160, hf160]


def squareColumn9part9Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD]

def squareColumn9part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 128
  let v1 : UInt256 := MachineState.readWord s.memory 64
  let v2 : UInt256 := UInt256.mulMod v1 v0 x0
  let v3 : UInt256 := v2 + x1
  let v4 : UInt256 := v3 + v3
  {s with pc := UInt256.ofNat 6947, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem squareColumn9part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part9Program {s with pc := UInt256.ofNat 6937, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (squareColumn9part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha128 : (128 : UInt256).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part9Program, squareColumn9part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha128, hf128]


def squareColumn9part10Program : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL]

def squareColumn9part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x2 + x0
  let v1 : UInt256 := x2 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 96
  let v3 : UInt256 := v2 * v2
  {s with pc := UInt256.ofNat 6956, memory := s.memory, stack := v3 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn9part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part10Program {s with pc := UInt256.ofNat 6947, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn9part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part10Program, squareColumn9part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96]


def squareColumn9part11Program : List Instr :=
  [.op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD]

def squareColumn9part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 192
  let v2 : UInt256 := x11 * v1
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 0
  {s with pc := UInt256.ofNat 6965, memory := s.memory, stack := v4 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn9part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part11Program {s with pc := UInt256.ofNat 6956, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn9part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : UInt256).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part11Program, squareColumn9part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0, ha192, hf192]


def squareColumn9part12Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD]

def squareColumn9part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x9 * x0
  let v1 : UInt256 := v0 + x1
  let v2 : UInt256 := MachineState.readWord s.memory 224
  let v3 : UInt256 := v2 * x4
  let v4 : UInt256 := v3 + v1
  {s with pc := UInt256.ofNat 6974, memory := s.memory, stack := v4 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem squareColumn9part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part12Program {s with pc := UInt256.ofNat 6965, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (squareColumn9part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, squareColumn9part12Program, squareColumn9part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224]


def squareColumn9part13Program : List Instr :=
  [.op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def squareColumn9part13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 6976, memory := s.memory, stack := x6 :: x7 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem squareColumn9part13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9part13Program {s with pc := UInt256.ofNat 6974, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (squareColumn9part13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, squareColumn9part13Program, squareColumn9part13Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def squareColumn9Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
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
   .push 2 768,
   .op .MSTORE,
   .push 1 16,
   .op .SHL,
   .op (.Swap ⟨0, by decide⟩),
   .push 1 240,
   .op .SHR,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .push 2 1280,
   .op .MLOAD,
   .op (.Swap ⟨13, by decide⟩),
   .op .POP,
   .op (.Swap ⟨7, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MUL,
   .push 1 160,
   .op .MLOAD,
   .push 1 32,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 64,
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
   .push 1 32,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .push 1 128,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 1 192,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]

def squareColumn9Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod carry word0 word1
  let v1 : UInt256 := v0 + word2
  let v2 : UInt256 := UInt256.mulMod word7 word16 word11
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := MachineState.readWord s.memory 1280
  let v5 : UInt256 := UInt256.mulMod v4 word4 word11
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := UInt256.mulMod word15 word13 word11
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.lnot word3
  let v10 : UInt256 := UInt256.addMod v8 v9 word11
  let v11 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 5)
  let v12 : UInt256 := UInt256.land word14 word3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : UInt256 := UInt256.shiftLeft v11 (UInt256.ofNat 16)
  let v15 : UInt256 := UInt256.shiftRight word3 (UInt256.ofNat 240)
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := MachineState.readWord v13 1216
  let v18 : UInt256 := MachineState.readWord v13 1280
  let v19 : UInt256 := word17 * word8
  let v20 : UInt256 := MachineState.readWord v13 160
  let v21 : UInt256 := MachineState.readWord v13 32
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := MachineState.readWord v13 128
  let v25 : UInt256 := MachineState.readWord v13 64
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := UInt256.mulMod word17 word8 word11
  let v30 : UInt256 := MachineState.readWord v13 160
  let v31 : UInt256 := MachineState.readWord v13 32
  let v32 : UInt256 := UInt256.mulMod v31 v30 word11
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := MachineState.readWord v13 128
  let v35 : UInt256 := MachineState.readWord v13 64
  let v36 : UInt256 := UInt256.mulMod v35 v34 word11
  let v37 : UInt256 := v36 + v33
  let v38 : UInt256 := v37 + v37
  let v39 : UInt256 := v16 + v38
  let v40 : UInt256 := v16 + v28
  let v41 : UInt256 := MachineState.readWord v13 96
  let v42 : UInt256 := v41 * v41
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := MachineState.readWord v13 192
  let v45 : UInt256 := word12 * v44
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := MachineState.readWord v13 0
  let v48 : UInt256 := word10 * v47
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := MachineState.readWord v13 224
  let v51 : UInt256 := v50 * word5
  let v52 : UInt256 := v51 + v49
  {s with pc := UInt256.ofNat 6976, memory := v13, stack := v17 :: word9 :: v52 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest}

theorem squareColumn9_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9Program {s with pc := UInt256.ofNat 6848, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} =
      some (squareColumn9Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 word16 word17 rest) := by
  let v0 : UInt256 := UInt256.mulMod carry word0 word1
  let v1 : UInt256 := v0 + word2
  let v2 : UInt256 := UInt256.mulMod word7 word16 word11
  let v3 : UInt256 := v2 + v1
  let v4 : UInt256 := MachineState.readWord s.memory 1280
  let v5 : UInt256 := UInt256.mulMod v4 word4 word11
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := UInt256.mulMod word15 word13 word11
  let v8 : UInt256 := v7 + v6
  let v9 : UInt256 := UInt256.lnot word3
  let v10 : UInt256 := UInt256.addMod v8 v9 word11
  let v11 : UInt256 := UInt256.shiftRight v10 (UInt256.ofNat 5)
  let v12 : UInt256 := UInt256.land word14 word3
  let v13 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v12.toNat 32) 768
  let v14 : UInt256 := UInt256.shiftLeft v11 (UInt256.ofNat 16)
  let v15 : UInt256 := UInt256.shiftRight word3 (UInt256.ofNat 240)
  let v16 : UInt256 := v15 + v14
  let v17 : UInt256 := MachineState.readWord v13 1216
  let v18 : UInt256 := MachineState.readWord v13 1280
  let v19 : UInt256 := word17 * word8
  let v20 : UInt256 := MachineState.readWord v13 160
  let v21 : UInt256 := MachineState.readWord v13 32
  let v22 : UInt256 := v21 * v20
  let v23 : UInt256 := v22 + v19
  let v24 : UInt256 := MachineState.readWord v13 128
  let v25 : UInt256 := MachineState.readWord v13 64
  let v26 : UInt256 := v25 * v24
  let v27 : UInt256 := v26 + v23
  let v28 : UInt256 := v27 + v27
  let v29 : UInt256 := UInt256.mulMod word17 word8 word11
  let v30 : UInt256 := MachineState.readWord v13 160
  let v31 : UInt256 := MachineState.readWord v13 32
  let v32 : UInt256 := UInt256.mulMod v31 v30 word11
  let v33 : UInt256 := v32 + v29
  let v34 : UInt256 := MachineState.readWord v13 128
  let v35 : UInt256 := MachineState.readWord v13 64
  let v36 : UInt256 := UInt256.mulMod v35 v34 word11
  let v37 : UInt256 := v36 + v33
  let v38 : UInt256 := v37 + v37
  let v39 : UInt256 := v16 + v38
  let v40 : UInt256 := v16 + v28
  let v41 : UInt256 := MachineState.readWord v13 96
  let v42 : UInt256 := v41 * v41
  let v43 : UInt256 := v42 + v40
  let v44 : UInt256 := MachineState.readWord v13 192
  let v45 : UInt256 := word12 * v44
  let v46 : UInt256 := v45 + v43
  let v47 : UInt256 := MachineState.readWord v13 0
  let v48 : UInt256 := word10 * v47
  let v49 : UInt256 := v48 + v46
  let v50 : UInt256 := MachineState.readWord v13 224
  let v51 : UInt256 := v50 * word5
  let v52 : UInt256 := v51 + v49
  have h0 : runInstructions squareColumn9part0Program {s with pc := UInt256.ofNat 6848, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6856, memory := s.memory, stack := word11 :: v3 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part0Model, v0, v1, v2, v3] using squareColumn9part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h1 : runInstructions squareColumn9part1Program {s with pc := UInt256.ofNat 6856, memory := s.memory, stack := word11 :: v3 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6866, memory := s.memory, stack := word15 :: word13 :: word11 :: v6 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part1Model, v4, v5, v6] using squareColumn9part1_run (s) (word11) (v3) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h2 : runInstructions squareColumn9part2Program {s with pc := UInt256.ofNat 6866, memory := s.memory, stack := word15 :: word13 :: word11 :: v6 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6875, memory := s.memory, stack := (UInt256.ofNat 5) :: v10 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part2Model, v7, v8, v9, v10] using squareColumn9part2_run (s) (word15) (word13) (word11) (v6) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h3 : runInstructions squareColumn9part3Program {s with pc := UInt256.ofNat 6875, memory := s.memory, stack := (UInt256.ofNat 5) :: v10 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6886, memory := v13, stack := v14 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part3Model, v11, v12, v13, v14] using squareColumn9part3_run (s) ((UInt256.ofNat 5)) (v10) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h4 : runInstructions squareColumn9part4Program {s with pc := UInt256.ofNat 6886, memory := v13, stack := v14 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6897, memory := v13, stack := v17 :: word11 :: word17 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part4Model, v15, v16, v17] using squareColumn9part4_run ({s with memory := v13}) (v14) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h5 : runInstructions squareColumn9part5Program {s with pc := UInt256.ofNat 6897, memory := v13, stack := v17 :: word11 :: word17 :: v16 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6907, memory := v13, stack := v19 :: word8 :: word11 :: word17 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part5Model, v18, v19] using squareColumn9part5_run ({s with memory := v13}) (v17) (word11) (word17) (v16) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) (word16) (word17) rest hcap hact
  have h6 : runInstructions squareColumn9part6Program {s with pc := UInt256.ofNat 6907, memory := v13, stack := v19 :: word8 :: word11 :: word17 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6918, memory := v13, stack := v24 :: v23 :: word8 :: word11 :: word17 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part6Model, v20, v21, v22, v23, v24] using squareColumn9part6_run ({s with memory := v13}) (v19) (word8) (word11) (word17) (v16) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h7 : runInstructions squareColumn9part7Program {s with pc := UInt256.ofNat 6918, memory := v13, stack := v24 :: v23 :: word8 :: word11 :: word17 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6927, memory := v13, stack := v29 :: v28 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part7Model, v25, v26, v27, v28, v29] using squareColumn9part7_run ({s with memory := v13}) (v24) (v23) (word8) (word11) (word17) (v16) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h8 : runInstructions squareColumn9part8Program {s with pc := UInt256.ofNat 6927, memory := v13, stack := v29 :: v28 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6937, memory := v13, stack := word11 :: v33 :: v28 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part8Model, v30, v31, v32, v33] using squareColumn9part8_run ({s with memory := v13}) (v29) (v28) (v16) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h9 : runInstructions squareColumn9part9Program {s with pc := UInt256.ofNat 6937, memory := v13, stack := word11 :: v33 :: v28 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6947, memory := v13, stack := v38 :: v28 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part9Model, v34, v35, v36, v37, v38] using squareColumn9part9_run ({s with memory := v13}) (word11) (v33) (v28) (v16) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h10 : runInstructions squareColumn9part10Program {s with pc := UInt256.ofNat 6947, memory := v13, stack := v38 :: v28 :: v16 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6956, memory := v13, stack := v42 :: v40 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part10Model, v39, v40, v41, v42] using squareColumn9part10_run ({s with memory := v13}) (v38) (v28) (v16) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h11 : runInstructions squareColumn9part11Program {s with pc := UInt256.ofNat 6956, memory := v13, stack := v42 :: v40 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6965, memory := v13, stack := v47 :: v46 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part11Model, v43, v44, v45, v46, v47] using squareColumn9part11_run ({s with memory := v13}) (v42) (v40) (v39) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h12 : runInstructions squareColumn9part12Program {s with pc := UInt256.ofNat 6965, memory := v13, stack := v47 :: v46 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6974, memory := v13, stack := v52 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part12Model, v48, v49, v50, v51, v52] using squareColumn9part12_run ({s with memory := v13}) (v47) (v46) (v39) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  have h13 : runInstructions squareColumn9part13Program {s with pc := UInt256.ofNat 6974, memory := v13, stack := v52 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} = some {s with pc := UInt256.ofNat 6976, memory := v13, stack := v17 :: word9 :: v52 :: v39 :: word4 :: word5 :: word6 :: word7 :: v17 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: word16 :: word17 :: rest} := by
    simpa only [squareColumn9part13Model] using squareColumn9part13_run ({s with memory := v13}) (v52) (v39) (word4) (word5) (word6) (word7) (v17) (word9) (word10) (word11) (word12) (v18) (word14) (word15) (word16) (word17) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 h13)))))))))))))


end CycleSubmission.Execution
