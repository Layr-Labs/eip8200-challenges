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

def productColumn10part0Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn10part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.mulMod x8 v1 x10
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 9034, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn10part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part0Program {s with pc := UInt256.ofNat 9026, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn10part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : UInt256).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part0Program, productColumn10part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha0, hf0]


def productColumn10part1Program : List Instr :=
  [.push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1216,
   .op .MLOAD]

def productColumn10part1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 224
  let v1 : UInt256 := UInt256.mulMod x5 v0 x0
  let v2 : UInt256 := v1 + x1
  let v3 : UInt256 := MachineState.readWord s.memory 1216
  {s with pc := UInt256.ofNat 9046, memory := s.memory, stack := v3 :: x15 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn10part1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part1Program {s with pc := UInt256.ofNat 9034, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn10part1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : UInt256).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : UInt256).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part1Program, productColumn10part1Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha224, hf224, ha1216, hf1216]


def productColumn10part2Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD]

def productColumn10part2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x0 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 1248
  let v3 : UInt256 := UInt256.mulMod v2 x18 x12
  {s with pc := UInt256.ofNat 9056, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn10part2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part2Program {s with pc := UInt256.ofNat 9046, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn10part2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part2Program, productColumn10part2Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def productColumn10part3Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn10part3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := MachineState.readWord s.memory 1280
  let v2 : UInt256 := UInt256.mulMod x12 v1 x10
  let v3 : UInt256 := v2 + v0
  {s with pc := UInt256.ofNat 9066, memory := s.memory, stack := x10 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn10part3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part3Program {s with pc := UInt256.ofNat 9056, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn10part3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1280 : (1280 : UInt256).toNat = 1280 := rfl
  have hf1280 := Monpro.activeWords_fix s 1280 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part3Program, productColumn10part3Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1280, hf1280]


def productColumn10part4Program : List Instr :=
  [.op (.Dup ⟨13, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def productColumn10part4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2720
  let v1 : UInt256 := x2 * v0
  let v2 : UInt256 := UInt256.land v1 x13
  {s with pc := UInt256.ofNat 9076, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn10part4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part4Program {s with pc := UInt256.ofNat 9066, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn10part4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : UInt256).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part4Program, productColumn10part4Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2720, hf2720]


def productColumn10part5Program : List Instr :=
  [.op (.Swap ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1248,
   .op .MLOAD]

def productColumn10part5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x16 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v1 x4
  let v3 : UInt256 := MachineState.readWord s.memory 1248
  {s with pc := UInt256.ofNat 9089, memory := s.memory, stack := v3 :: x12 :: v2 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x0 :: x17 :: x18 :: rest}

theorem productColumn10part5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part5Program {s with pc := UInt256.ofNat 9076, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn10part5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1248 : (1248 : UInt256).toNat = 1248 := rfl
  have hf1248 := Monpro.activeWords_fix s 1248 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part5Program, productColumn10part5Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha1248, hf1248]


def productColumn10part6Program : List Instr :=
  [.op (.Swap ⟨6, by decide⟩),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD]

def productColumn10part6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 2048
  let v1 : UInt256 := v0 * x7
  let v2 : UInt256 := v1 + x3
  {s with pc := UInt256.ofNat 9099, memory := s.memory, stack := v2 :: x7 :: x1 :: x2 :: v0 :: x4 :: x5 :: x6 :: x0 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem productColumn10part6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part6Program {s with pc := UInt256.ofNat 9089, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (productColumn10part6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : UInt256).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part6Program, productColumn10part6Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2048, hf2048]


def productColumn10part7Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩)]

def productColumn10part7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.mulMod x4 x1 x2
  let v1 : UInt256 := v0 + x3
  let v2 : UInt256 := MachineState.readWord s.memory 2016
  {s with pc := UInt256.ofNat 9109, memory := s.memory, stack := x0 :: x9 :: x12 :: v1 :: v2 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn10part7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part7Program {s with pc := UInt256.ofNat 9099, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn10part7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha2016 : (2016 : UInt256).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part7Program, productColumn10part7Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha2016, hf2016]


def productColumn10part8Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def productColumn10part8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x4 * x1
  let v1 : UInt256 := v0 + x0
  let v2 : UInt256 := UInt256.mulMod x4 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9117, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn10part8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part8Program {s with pc := UInt256.ofNat 9109, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn10part8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn10part8Program, productColumn10part8Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn10part9Program : List Instr :=
  [.push 1 32,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL]

def productColumn10part9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 32
  let v1 : UInt256 := MachineState.readWord s.memory 1984
  let v2 : UInt256 := v1 * v0
  {s with pc := UInt256.ofNat 9128, memory := s.memory, stack := v2 :: x2 :: v0 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem productColumn10part9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part9Program {s with pc := UInt256.ofNat 9117, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (productColumn10part9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : UInt256).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : UInt256).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part9Program, productColumn10part9Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha32, hf32, ha1984, hf1984]


def productColumn10part10Program : List Instr :=
  [.op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD]

def productColumn10part10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 + x1
  let v1 : UInt256 := UInt256.mulMod x5 x2 x3
  let v2 : UInt256 := v1 + x4
  let v3 : UInt256 := MachineState.readWord s.memory 64
  let v4 : UInt256 := MachineState.readWord s.memory 1952
  {s with pc := UInt256.ofNat 9140, memory := s.memory, stack := v4 :: v3 :: x13 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem productColumn10part10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part10Program {s with pc := UInt256.ofNat 9128, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (productColumn10part10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : UInt256).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : UInt256).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part10Program, productColumn10part10Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha64, hf64, ha1952, hf1952]


def productColumn10part11Program : List Instr :=
  [.op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def productColumn10part11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := x0 * x1
  let v1 : UInt256 := v0 + x4
  let v2 : UInt256 := UInt256.mulMod x0 x1 x2
  let v3 : UInt256 := v2 + x3
  {s with pc := UInt256.ofNat 9148, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem productColumn10part11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part11Program {s with pc := UInt256.ofNat 9140, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (productColumn10part11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, productColumn10part11Program, productColumn10part11Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def productColumn10part12Program : List Instr :=
  [.op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD]

def productColumn10part12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 96
  let v1 : UInt256 := MachineState.readWord s.memory 1920
  {s with pc := UInt256.ofNat 9156, memory := s.memory, stack := v1 :: v0 :: x9 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem productColumn10part12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10part12Program {s with pc := UInt256.ofNat 9148, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (productColumn10part12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : UInt256).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : UInt256).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, productColumn10part12Program, productColumn10part12Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha96, hf96, ha1920, hf1920]


def productColumn10Program : List Instr :=
  [.op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1280,
   .op .MLOAD,
   .op (.Dup ⟨13, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨13, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨15, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .push 2 1248,
   .op .MLOAD,
   .op (.Swap ⟨6, by decide⟩),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
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
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 96,
   .op .MLOAD,
   .push 2 1920,
   .op .MLOAD]

def productColumn10Model (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.mulMod word7 v1 word9
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 224
  let v5 : UInt256 := UInt256.mulMod word4 v4 word9
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := MachineState.readWord s.memory 1216
  let v8 : UInt256 := UInt256.mulMod v7 word14 word9
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := MachineState.readWord s.memory 1248
  let v11 : UInt256 := UInt256.mulMod v10 word15 word9
  let v12 : UInt256 := v11 + v9
  let v13 : UInt256 := MachineState.readWord s.memory 1280
  let v14 : UInt256 := UInt256.mulMod word11 v13 word9
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := MachineState.readWord s.memory 2720
  let v17 : UInt256 := word1 * v16
  let v18 : UInt256 := UInt256.land v17 word12
  let v19 : UInt256 := UInt256.mulMod word13 v18 word9
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v20 word9
  let v22 : UInt256 := MachineState.readWord s.memory 1248
  let v23 : UInt256 := MachineState.readWord s.memory 2048
  let v24 : UInt256 := v23 * word5
  let v25 : UInt256 := v24 + v21
  let v26 : UInt256 := UInt256.mulMod v23 word5 word9
  let v27 : UInt256 := v26 + v21
  let v28 : UInt256 := MachineState.readWord s.memory 2016
  let v29 : UInt256 := v28 * word6
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := UInt256.mulMod v28 word6 word9
  let v32 : UInt256 := v31 + v27
  let v33 : UInt256 := MachineState.readWord s.memory 32
  let v34 : UInt256 := MachineState.readWord s.memory 1984
  let v35 : UInt256 := v34 * v33
  let v36 : UInt256 := v35 + v30
  let v37 : UInt256 := UInt256.mulMod v34 v33 word9
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := MachineState.readWord s.memory 64
  let v40 : UInt256 := MachineState.readWord s.memory 1952
  let v41 : UInt256 := v40 * v39
  let v42 : UInt256 := v41 + v36
  let v43 : UInt256 := UInt256.mulMod v40 v39 word9
  let v44 : UInt256 := v43 + v38
  let v45 : UInt256 := MachineState.readWord s.memory 96
  let v46 : UInt256 := MachineState.readWord s.memory 1920
  {s with pc := UInt256.ofNat 9156, memory := s.memory, stack := v46 :: v45 :: word9 :: v44 :: v42 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest}

theorem productColumn10_run (s : State) (carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10Program {s with pc := UInt256.ofNat 9026, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} =
      some (productColumn10Model s carry word0 word1 word2 word3 word4 word5 word6 word7 word8 word9 word10 word11 word12 word13 word14 word15 rest) := by
  let v0 : UInt256 := carry + word0
  let v1 : UInt256 := MachineState.readWord s.memory 0
  let v2 : UInt256 := UInt256.mulMod word7 v1 word9
  let v3 : UInt256 := v2 + v0
  let v4 : UInt256 := MachineState.readWord s.memory 224
  let v5 : UInt256 := UInt256.mulMod word4 v4 word9
  let v6 : UInt256 := v5 + v3
  let v7 : UInt256 := MachineState.readWord s.memory 1216
  let v8 : UInt256 := UInt256.mulMod v7 word14 word9
  let v9 : UInt256 := v8 + v6
  let v10 : UInt256 := MachineState.readWord s.memory 1248
  let v11 : UInt256 := UInt256.mulMod v10 word15 word9
  let v12 : UInt256 := v11 + v9
  let v13 : UInt256 := MachineState.readWord s.memory 1280
  let v14 : UInt256 := UInt256.mulMod word11 v13 word9
  let v15 : UInt256 := v14 + v12
  let v16 : UInt256 := MachineState.readWord s.memory 2720
  let v17 : UInt256 := word1 * v16
  let v18 : UInt256 := UInt256.land v17 word12
  let v19 : UInt256 := UInt256.mulMod word13 v18 word9
  let v20 : UInt256 := v19 + v15
  let v21 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v20 word9
  let v22 : UInt256 := MachineState.readWord s.memory 1248
  let v23 : UInt256 := MachineState.readWord s.memory 2048
  let v24 : UInt256 := v23 * word5
  let v25 : UInt256 := v24 + v21
  let v26 : UInt256 := UInt256.mulMod v23 word5 word9
  let v27 : UInt256 := v26 + v21
  let v28 : UInt256 := MachineState.readWord s.memory 2016
  let v29 : UInt256 := v28 * word6
  let v30 : UInt256 := v29 + v25
  let v31 : UInt256 := UInt256.mulMod v28 word6 word9
  let v32 : UInt256 := v31 + v27
  let v33 : UInt256 := MachineState.readWord s.memory 32
  let v34 : UInt256 := MachineState.readWord s.memory 1984
  let v35 : UInt256 := v34 * v33
  let v36 : UInt256 := v35 + v30
  let v37 : UInt256 := UInt256.mulMod v34 v33 word9
  let v38 : UInt256 := v37 + v32
  let v39 : UInt256 := MachineState.readWord s.memory 64
  let v40 : UInt256 := MachineState.readWord s.memory 1952
  let v41 : UInt256 := v40 * v39
  let v42 : UInt256 := v41 + v36
  let v43 : UInt256 := UInt256.mulMod v40 v39 word9
  let v44 : UInt256 := v43 + v38
  let v45 : UInt256 := MachineState.readWord s.memory 96
  let v46 : UInt256 := MachineState.readWord s.memory 1920
  have h0 : runInstructions productColumn10part0Program {s with pc := UInt256.ofNat 9026, memory := s.memory, stack := carry :: word0 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9034, memory := s.memory, stack := word9 :: v3 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part0Model, v0, v1, v2, v3] using productColumn10part0_run (s) (carry) (word0) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h1 : runInstructions productColumn10part1Program {s with pc := UInt256.ofNat 9034, memory := s.memory, stack := word9 :: v3 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9046, memory := s.memory, stack := v7 :: word14 :: word9 :: v6 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part1Model, v4, v5, v6, v7] using productColumn10part1_run (s) (word9) (v3) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h2 : runInstructions productColumn10part2Program {s with pc := UInt256.ofNat 9046, memory := s.memory, stack := v7 :: word14 :: word9 :: v6 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9056, memory := s.memory, stack := v11 :: v9 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part2Model, v8, v9, v10, v11] using productColumn10part2_run (s) (v7) (word14) (word9) (v6) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h3 : runInstructions productColumn10part3Program {s with pc := UInt256.ofNat 9056, memory := s.memory, stack := v11 :: v9 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9066, memory := s.memory, stack := word9 :: v15 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part3Model, v12, v13, v14, v15] using productColumn10part3_run (s) (v11) (v9) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h4 : runInstructions productColumn10part4Program {s with pc := UInt256.ofNat 9066, memory := s.memory, stack := word9 :: v15 :: word1 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9076, memory := s.memory, stack := v18 :: v18 :: word9 :: v15 :: word9 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part4Model, v16, v17, v18] using productColumn10part4_run (s) (word9) (v15) (word1) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h5 : runInstructions productColumn10part5Program {s with pc := UInt256.ofNat 9076, memory := s.memory, stack := v18 :: v18 :: word9 :: v15 :: word9 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: word13 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9089, memory := s.memory, stack := v22 :: word9 :: v21 :: v21 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part5Model, v19, v20, v21, v22] using productColumn10part5_run (s) (v18) (v18) (word9) (v15) (word9) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (word13) (word14) (word15) rest hcap hact
  have h6 : runInstructions productColumn10part6Program {s with pc := UInt256.ofNat 9089, memory := s.memory, stack := v22 :: word9 :: v21 :: v21 :: word2 :: word3 :: word4 :: word5 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9099, memory := s.memory, stack := v25 :: word5 :: word9 :: v21 :: v23 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part6Model, v23, v24, v25] using productColumn10part6_run (s) (v22) (word9) (v21) (v21) (word2) (word3) (word4) (word5) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  have h7 : runInstructions productColumn10part7Program {s with pc := UInt256.ofNat 9099, memory := s.memory, stack := v25 :: word5 :: word9 :: v21 :: v23 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9109, memory := s.memory, stack := v25 :: word6 :: word9 :: v27 :: v28 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part7Model, v26, v27, v28] using productColumn10part7_run (s) (v25) (word5) (word9) (v21) (v23) (word2) (word3) (word4) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  have h8 : runInstructions productColumn10part8Program {s with pc := UInt256.ofNat 9109, memory := s.memory, stack := v25 :: word6 :: word9 :: v27 :: v28 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9117, memory := s.memory, stack := word9 :: v32 :: v30 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part8Model, v29, v30, v31, v32] using productColumn10part8_run (s) (v25) (word6) (word9) (v27) (v28) (word2) (word3) (word4) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  have h9 : runInstructions productColumn10part9Program {s with pc := UInt256.ofNat 9117, memory := s.memory, stack := word9 :: v32 :: v30 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9128, memory := s.memory, stack := v35 :: v30 :: v33 :: word9 :: v32 :: v34 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part9Model, v33, v34, v35] using productColumn10part9_run (s) (word9) (v32) (v30) (word2) (word3) (word4) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  have h10 : runInstructions productColumn10part10Program {s with pc := UInt256.ofNat 9128, memory := s.memory, stack := v35 :: v30 :: v33 :: word9 :: v32 :: v34 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9140, memory := s.memory, stack := v40 :: v39 :: word9 :: v38 :: v36 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part10Model, v36, v37, v38, v39, v40] using productColumn10part10_run (s) (v35) (v30) (v33) (word9) (v32) (v34) (word2) (word3) (word4) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  have h11 : runInstructions productColumn10part11Program {s with pc := UInt256.ofNat 9140, memory := s.memory, stack := v40 :: v39 :: word9 :: v38 :: v36 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9148, memory := s.memory, stack := v44 :: v42 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part11Model, v41, v42, v43, v44] using productColumn10part11_run (s) (v40) (v39) (word9) (v38) (v36) (word2) (word3) (word4) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  have h12 : runInstructions productColumn10part12Program {s with pc := UInt256.ofNat 9148, memory := s.memory, stack := v44 :: v42 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} = some {s with pc := UInt256.ofNat 9156, memory := s.memory, stack := v46 :: v45 :: word9 :: v44 :: v42 :: word2 :: word3 :: word4 :: v22 :: word6 :: word7 :: word8 :: word9 :: word10 :: word11 :: word12 :: v18 :: word14 :: word15 :: rest} := by
    simpa only [productColumn10part12Model, v45, v46] using productColumn10part12_run (s) (v44) (v42) (word2) (word3) (word4) (v22) (word6) (word7) (word8) (word9) (word10) (word11) (word12) (v18) (word14) (word15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 h12))))))))))))


end CycleSubmission.Execution
